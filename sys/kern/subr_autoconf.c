/*
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
 *
 * This software was developed by the Computer Systems Engineering group
 * at Lawrence Berkeley Laboratory under DARPA contract BG 91-66 and
 * contributed to Berkeley.
 *
 * All advertising materials mentioning features or use of this software
 * must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Lawrence Berkeley Laboratories.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 *	@(#)subr_autoconf.c	8.1 (Berkeley) 6/10/93
 *
 * $FreeBSD: src/sys/kern/subr_autoconf.c,v 1.14 1999/10/05 21:19:41 n_hibma Exp $
 * $DragonFly: src/sys/kern/subr_autoconf.c,v 1.9 2007/07/28 23:24:33 dillon Exp $
 */

#include <sys/param.h>
#include <sys/kernel.h>
#include <sys/systm.h>
#include <sys/thread.h>
#include <sys/thread2.h>

/*
 * Autoconfiguration subroutines.
 */

/*
 * "Interrupt driven config" functions.
 */
static TAILQ_HEAD(, intr_config_hook) intr_config_hook_list =
	TAILQ_HEAD_INITIALIZER(intr_config_hook_list);


/* ARGSUSED */
static void run_interrupt_driven_config_hooks (void *dummy);
static int ran_config_hooks;

static void
run_interrupt_driven_config_hooks(void *dummy)
{
	struct intr_config_hook *hook_entry;
	int waiting;

	waiting = 0;

	ran_config_hooks = 1;
	while (!TAILQ_EMPTY(&intr_config_hook_list)) {
		TAILQ_FOREACH(hook_entry, &intr_config_hook_list, ich_links) {
			if (hook_entry->ich_ran == 0) {
				hook_entry->ich_ran = 1;
				(*hook_entry->ich_func)(hook_entry->ich_arg);
				break;
			}
		}
		if (hook_entry)
			continue;
		if (TAILQ_EMPTY(&intr_config_hook_list))
			break;

		if (waiting >= 20 && (waiting % 10) == 0) {
			crit_enter();
			kprintf("**WARNING** waiting for the following device "
				"to finish configuring:\n");
			TAILQ_FOREACH(hook_entry, &intr_config_hook_list,
				      ich_links) {
			    kprintf("  %s:\tfunc=%p arg=%p\n",
				(hook_entry->ich_desc ?
				    hook_entry->ich_desc : "?"),
				hook_entry->ich_func,
				hook_entry->ich_arg);
			}
			crit_exit();
			if (waiting >= 60) {
				kprintf("Giving up, interrupt routing is "
					"probably hosed\n");
				break;
			}
		}
		tsleep(&intr_config_hook_list, 0, "conifhk", hz);
		++waiting;
	}
}
SYSINIT(intr_config_hooks, SI_SUB_INT_CONFIG_HOOKS, SI_ORDER_FIRST,
	run_interrupt_driven_config_hooks, NULL)

/*
 * Register a hook that will be called after "cold"
 * autoconfiguration is complete and interrupts can
 * be used to complete initialization.
 */
int
config_intrhook_establish(struct intr_config_hook *hook)
{
	struct intr_config_hook *hook_entry;

	for (hook_entry = TAILQ_FIRST(&intr_config_hook_list);
	     hook_entry != NULL;
	     hook_entry = TAILQ_NEXT(hook_entry, ich_links)) {
		if (hook_entry == hook)
			break;
		if (hook_entry->ich_order > hook->ich_order)
			break;
	}
	if (hook_entry == hook) {
		kprintf("config_intrhook_establish: establishing an "
		       "already established hook.\n");
		return (1);
	}
	hook->ich_ran = 0;
	if (hook_entry)
		TAILQ_INSERT_BEFORE(hook_entry, hook, ich_links);
	else
		TAILQ_INSERT_TAIL(&intr_config_hook_list, hook, ich_links);

	/*
	 * Late hook, run immediately.
	 */
	if (ran_config_hooks)
		run_interrupt_driven_config_hooks(NULL);	
	return (0);
}

void
config_intrhook_disestablish(struct intr_config_hook *hook)
{
	struct intr_config_hook *hook_entry;

	for (hook_entry = TAILQ_FIRST(&intr_config_hook_list);
	     hook_entry != NULL;
	     hook_entry = TAILQ_NEXT(hook_entry, ich_links))
		if (hook_entry == hook)
			break;
	if (hook_entry == NULL)
		panic("config_intrhook_disestablish: disestablishing an "
		    "unestablished hook");

	TAILQ_REMOVE(&intr_config_hook_list, hook, ich_links);
	/* Wakeup anyone watching the list */
	wakeup(&intr_config_hook_list);
}
