#include <sys/async_kexec.h>
#include <sys/event.h>
#include <sys/file.h>
#include <sys/filedesc.h>
#include <sys/kernel.h>
#include <sys/kthread.h>
#include <sys/proc.h>
#include <sys/spinlock2.h>
#include <sys/syscall.h>
#include <sys/sysent.h>
#include <sys/sysproto.h>
#include <sys/systm.h>
#include <sys/sysunion.h>
#include <sys/thread2.h>

#include <vm/pmap.h>

MALLOC_DEFINE(M_KCALL, "kcall", "kcall");

#define	KCALL_CANCELED	1
#define KCALL_FINISHED	2

struct kcall {
	struct async_kcall	*kc_next;
	struct proc			*kc_owner;
	struct kqinfo		kc_kq;	
	int					kc_flags;
	int					kc_cancel;
	struct lwkt_token	kc_token;
	struct lwp			*kc_lwp;
};

struct work_thread_args {
	struct lwp			*wt_lwp;
	struct kcall		*wt_kcall;
	int					wt_async;
};

static int kcall_read(struct file *fp, struct uio *uio, struct ucred *cred,
	int flags);
static int kcall_write(struct file *fp, struct uio *uio, struct ucred *cred,
	int flags);
static int kcall_kqfilter(struct file *fp, struct knote *kn);
static int kcall_ioctl(struct file *fp, u_long com, caddr_t data,
	struct ucred *cred, struct sysmsg *msg);
static int kcall_stat(struct file *fp, struct stat *st, struct ucred *cred);
static int kcall_close(struct file *fp);

static struct fileops kcallops = {
	.fo_read = kcall_read,
	.fo_write = kcall_write,
	.fo_ioctl = kcall_ioctl,
	.fo_kqfilter = kcall_kqfilter,
	.fo_stat = kcall_stat,
	.fo_close = kcall_close,
	.fo_shutdown = nofo_shutdown
};

static int enqueue_kcall(struct kcall *kc, struct proc* p, int flags);
static void work_thread(void* ptr);

static void	filt_kcalldetach(struct knote *kn);
static int	filt_kcall(struct knote *kn, long hint);

static struct filterops kcall_filtops =
	{ FILTEROP_ISFD | FILTEROP_MPSAFE, NULL, filt_kcalldetach, filt_kcall };

static struct lwp *create_work_thread(struct work_thread_args *args)
{
	struct thread *td;
	struct lwp *lp;

	td = lwkt_alloc_thread(NULL, LWKT_THREAD_STACK, -1, 0);

	td->td_ucred = crhold(proc0.p_ucred);
	lwkt_set_comm(td, "async_kexec work thread");

	cpu_set_thread_handler(td, kthread_exit, work_thread, args);

	lp = kmalloc(sizeof(struct lwp), M_LWP, M_WAITOK|M_ZERO);
	lp->lwp_thread = td;
	lp->lwp_stat = LSRUN;
	lp->lwp_flags = LWP_ALTSTACK;
	SIGFILLSET(lp->lwp_sigmask);

	lwkt_token_init(&lp->lwp_token, "lwp_token");
	spin_init(&lp->lwp_spin);

	args->wt_lwp = lp;

	lwkt_schedule(td);
	return lp;
}

static void attach_work_thread(struct lwp *lp, struct proc *p)
{
	struct thread *td = lp->lwp_thread;

	lwkt_gettoken(&p->p_token);
	plimit_lwp_fork(p);

	lp->lwp_proc = p;
	lp->lwp_vmspace = p->p_vmspace;

	td->td_lwp = lp;
	td->td_proc = p;
	td->td_switch = cpu_heavy_switch;

	crfree(td->td_ucred);
	td->td_ucred = crhold(p->p_ucred);

	kqueue_init(&lp->lwp_kqueue, p->p_fd);

	lp->lwp_tid = p->p_lasttid;
	do {
		if (++lp->lwp_tid < 0)
		lp->lwp_tid = 1;
	} while (lwp_rb_tree_RB_INSERT(&p->p_lwp_tree, lp) != NULL);
	p->p_lasttid = lp->lwp_tid;

	p->p_nthreads++;

	lwkt_setpri(td, TDPRI_KERN_USER);
	pmap_reloadvm();
}

static void detach_work_thread(struct lwp *lp)
{
	struct proc *p = lp->lwp_proc;
	struct thread *td = lp->lwp_thread;

	lwkt_setpri(td, TDPRI_KERN_DAEMON);

	lwkt_gettoken(&p->p_token);
	plimit_lwp_fork(p);

	lwp_rb_tree_RB_REMOVE(&p->p_lwp_tree, lp);
	--p->p_nthreads;

	lp->lwp_proc = NULL;
	lp->lwp_vmspace = NULL;
	lp->lwp_stat = LSRUN;

	kqueue_terminate(&lp->lwp_kqueue);

	crfree(td->td_ucred);
	td->td_ucred = crhold(proc0.p_ucred);

	td->td_lwp = NULL;
	td->td_proc = NULL;
	td->td_switch = cpu_lwkt_switch;

	lwkt_reltoken(&p->p_token);
}

/* XXX prototype */
static int
do_syscall(struct async_kcall *ak)
{
	int error;
	int i;
	struct sysent *callp;

	struct proc *p = curproc;

	union sysunion args;
	uint8_t *args_ptr;

	//kprintf("ASYNC_KEXEC: ak_syscall: %u, ak_next: %p, p: %p\n",
	//	ak->ak_syscall, ak->ak_next, p);

	/* XXX make sure that arg_len given by user does not cause the stack
	   to be overriden */
	args_ptr = (uint8_t*)(&args.nosys.sysmsg + 1);
	for (i = 0; i < ak->ak_arg_count; i++) {
		error = copyin(ak->ak_args[i], args_ptr, ak->ak_arg_lens[i]);
		if (error)
			goto out;

		args_ptr += sizeof(register_t); //ak->ak_arg_lens[i];
	}

	/* XXX call syscall precall */

	/* XXX make sure that we do almost everything syscall2() does */

	if (ak->ak_syscall >= p->p_sysent->sv_size)
		callp = &p->p_sysent->sv_table[0];
	else
		callp = &p->p_sysent->sv_table[ak->ak_syscall];

	error = (*callp->sy_call)(&args);

out:
	//kprintf("ASYNC_KEXEC exit %d\n", error);
	return error;
}

static inline void
work_thread_yield(void)
{
	lwkt_setpri_self(TDPRI_USER_NORM);
	lwkt_user_yield();
	lwkt_setpri_self(TDPRI_KERN_USER);
}

static void
work_thread(void* ptr)
{
	int error;
	struct async_kcall ak;

	struct work_thread_args *args = (struct work_thread_args *)ptr;
	struct lwp *lp = args->wt_lwp;
	struct kcall *kc = args->wt_kcall;
	int is_async = args->wt_async;
	kfree(args, M_TEMP);

	kprintf("ARGS: %p %p %u\n", lp, kc, is_async);
	kprintf("ATTACH\n");

//	lwkt_gettoken(&kc->kc_token);
	if (is_async)
		attach_work_thread(lp, kc->kc_owner);
	kc->kc_lwp = lp;
//	lwkt_reltoken(&kc->kc_token);

	do {
		//kprintf("COPYIN %p -> %p\n", kc->kc_next, &ak);
		error = copyin(kc->kc_next, &ak, sizeof(struct async_kcall));
		if (error)
			goto out;

		//kprintf("DO SYSCALL %u\n", ak.ak_syscall);
		error = do_syscall(&ak);
		if (error)
			goto out;

		kc->kc_next = ak.ak_next;
		if (!kc->kc_next || kc->kc_cancel)
			goto out;

		work_thread_yield();
	} while (1);

out:
	//kprintf("DETACH\n");
	if (is_async)
		detach_work_thread(lp);

	//kprintf("NOTIFY KQUEUE\n");

	lwkt_gettoken(&kc->kc_token);
	kc->kc_lwp = NULL;
	kc->kc_cancel |= KCALL_FINISHED;
	wakeup(&kc);
	lwkt_reltoken(&kc->kc_token);

	KNOTE(&kc->kc_kq.ki_note, 0);

	//kprintf("FINISHED\n");
}

static int
enqueue_kcall(struct kcall *kc, struct proc* p, int flags)
{
	int error = 0;
	struct work_thread_args *args;

	args = kmalloc(sizeof(struct work_thread_args), M_TEMP, M_WAITOK);

	args->wt_kcall = kc;
	args->wt_async = 1; //!(flags & KC_SYNCHRONOUS);
	args->wt_lwp = curthread->td_lwp;

	if (args->wt_async)
		create_work_thread(args);
	else
		work_thread(args);

	//kprintf("ENQUEUED\n");

	return error;
}

static int kcall_register_kevent(int fd, int kqd, struct kevent* event)
{
	struct proc *p = curproc;
	struct file *fp;
	struct kqueue *kq;
	struct kevent ev;
	struct lwkt_token *tok;
	int error;

	fp = holdfp(p->p_fd, kqd, -1);
	if (fp == NULL)
		return EBADF;
	if (fp->f_type != DTYPE_KQUEUE) {
		fdrop(fp);
		return EBADF;
	}
	kq = (struct kqueue *)fp->f_data;

	error = copyin(event, &ev, sizeof(struct kevent));
	if (error)
		return error;

	ev.ident = fd;
	ev.filter = EVFILT_READ;
	ev.flags |= EV_ADD;

	tok = lwkt_token_pool_lookup(kq);
	lwkt_gettoken(tok);
	error = kqueue_register(kq, &ev);
	lwkt_reltoken(tok);
	if (error) {
		ev.flags = EV_ERROR;
		ev.data = error;
	}

	error = copyout(&ev, event, sizeof(struct kevent));

	fdrop(fp);
	return error;
}

int
sys_async_kexec(struct async_kexec_args* uap)
{
	int fd, error;
	struct kcall *kc;
	struct file *fp;

	error = falloc(curthread->td_lwp, &fp, &fd);
	if (error)
		return error;
	fp->f_flag = FREAD | FWRITE;
	fp->f_type = DTYPE_MQUEUE + 1;
	fp->f_ops = &kcallops;

	kc = kmalloc(sizeof(struct kcall), M_KCALL, M_WAITOK | M_ZERO);
	kc->kc_next = uap->call;
	kc->kc_owner = curproc;
	kc->kc_flags = uap->flags;
	lwkt_token_init(&kc->kc_token, NULL);

	fp->f_data = kc;

	fsetfd(curproc->p_fd, fp, fd);
	fdrop(fp);

	if (uap->flags & KC_KEVENT) {
		error = kcall_register_kevent(fd, uap->fd, uap->event);
		if (error)
			return error;
	}

	error = enqueue_kcall(kc, curproc, uap->flags);
	if (error)
		return error; /* XXX: release fd */

	uap->sysmsg_result = fd;
	return error;
}

static int kcall_read(struct file *fp, struct uio *uio, struct ucred *cred,
	int flags)
{
	return ENXIO;
}

static int kcall_write(struct file *fp, struct uio *uio, struct ucred *cred,
	int flags)
{
	return ENXIO;
}

static int kcall_ioctl(struct file *fp, u_long com, caddr_t data,
	struct ucred *cred, struct sysmsg *msg)
{
	/* XXX: cancel, start */
	return 0;
}

static int kcall_stat(struct file *fp, struct stat *st, struct ucred *cred)
{
	return 0;
}

static int kcall_close(struct file *fp)
{
	struct kcall *kc = (struct kcall *)fp->f_data;

	//kprintf("CLOSING\n");

	lwkt_gettoken(&kc->kc_token);
	LWPHOLD(kc->kc_lwp);
	kc->kc_cancel |= KCALL_CANCELED;

	if (!(kc->kc_cancel & KCALL_FINISHED)) {
		tsleep_interlock(&kc, 0);
		lwkt_reltoken(&kc->kc_token);

		lwpsignal(kc->kc_owner, kc->kc_lwp, SIGINT);
		LWPRELE(kc->kc_lwp);

		tsleep(&kc, PINTERLOCKED, "kcall", 0);
	} else {
		LWPRELE(kc->kc_lwp);
		lwkt_reltoken(&kc->kc_token);
	}

	//kprintf("CLOSED\n");

	lwkt_token_uninit(&kc->kc_token);
	kfree(kc, M_KCALL);
	return 0;
}

/* XXX: notify per tag, each kcall element may have its own tag */
static int
kcall_kqfilter(struct file *fp, struct knote *kn)
{
	struct kcall *kc = (struct kcall *)kn->kn_fp->f_data;

	switch (kn->kn_filter) {
		case EVFILT_READ:
			kn->kn_fop = &kcall_filtops;
			break;
		default:
			return EOPNOTSUPP;
	}
	kn->kn_hook = (caddr_t)kc;

	knote_insert(&kc->kc_kq.ki_note, kn);

	//kprintf("ATTACHED NOTE %p\n", kn);
	return 0;
}

static void
filt_kcalldetach(struct knote *kn)
{
	struct kcall *kc = (struct kcall *)kn->kn_hook;

	knote_remove(&kc->kc_kq.ki_note, kn);

	//kprintf("DETACHED NOTE %p\n", kn);
}

static int
filt_kcall(struct knote *kn, long hint)
{
	struct kcall *kc = (struct kcall *)kn->kn_fp->f_data;

	//if (!kc->kc_next)
	//	kprintf("NOTIFIED %p %#lx\n", kn, hint);

	return !kc->kc_next;
}

