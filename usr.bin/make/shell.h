/*-
 * Copyright (c) 1988, 1989, 1990, 1993
 *	The Regents of the University of California.  All rights reserved.
 * Copyright (c) 1988, 1989 by Adam de Boor
 * Copyright (c) 1989 by Berkeley Softworks
 * All rights reserved.
 *
 * This code is derived from software contributed to Berkeley by
 * Adam de Boor.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *	This product includes software developed by the University of
 *	California, Berkeley and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
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
 * $DragonFly: src/usr.bin/make/shell.h,v 1.1 2005/05/19 16:53:58 okumoto Exp $
 */

#ifndef shell_h_6002e3b8
#define	shell_h_6002e3b8

#include "util.h"

/*
 * Shell Specifications:
 *
 * Some special stuff goes on if a shell doesn't have error control. In such
 * a case, errCheck becomes a printf template for echoing the command,
 * should echoing be on and ignErr becomes another printf template for
 * executing the command while ignoring the return status. If either of these
 * strings is empty when hasErrCtl is FALSE, the command will be executed
 * anyway as is and if it causes an error, so be it.
 */
#define	DEF_SHELL_STRUCT(TAG, CONST)					\
struct TAG {								\
	/*								\
	 * the name of the shell. For Bourne and C shells, this is used	\
	 * only to find the shell description when used as the single	\
	 * source of a .SHELL target. For user-defined shells, this is	\
	 * the full path of the shell.					\
	 */								\
	CONST char	*name;						\
									\
	/* True if both echoOff and echoOn defined */			\
	Boolean		hasEchoCtl;					\
									\
	CONST char	*echoOff;	/* command to turn off echo */	\
	CONST char	*echoOn;	/* command to turn it back on */\
									\
	/*								\
	 * What the shell prints, and its length, when given the	\
	 * echo-off command. This line will not be printed when		\
	 * received from the shell. This is usually the command which	\
	 * was executed to turn off echoing				\
	 */								\
	CONST char	*noPrint;					\
									\
	/* set if can control error checking for individual commands */	\
	Boolean		hasErrCtl;					\
									\
	/* string to turn error checking on */				\
	CONST char	*errCheck;					\
									\
	/* string to turn off error checking */				\
	CONST char	*ignErr;					\
									\
	CONST char	*echo;	/* command line flag: echo commands */	\
	CONST char	*exit;	/* command line flag: exit on error */	\
}

DEF_SHELL_STRUCT(Shell,);
DEF_SHELL_STRUCT(CShell, const);

extern char			*shellPath;
extern struct Shell		*commandShell;

void				Shell_Init(void);
Boolean				Job_ParseShell(const char []);

#endif /* shell_h_6002e3b8 */
