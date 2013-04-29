#ifndef _SYS_ASYNC_KEXEC_H_
#define _SYS_ASYNC_KEXEC_H_

#ifndef _SYS_TYPES_H_
#include <sys/types.h>
#endif

#define KC_ASYNCHRONOUS		1
#define	KC_SYNCHRONOUS		2
#define KC_KEVENT			4

struct async_kcall {
	u_int				ak_syscall;

	void				*ak_args[5];
	u_int				ak_arg_lens[5];
	u_int				ak_arg_count;

	struct async_kcall	*ak_next;
};

#endif /* !_SYS_ASYNC_KEXEC_H_ */
