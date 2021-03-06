/*-
 * Copyright (c) 1992, 1993
 *	The Regents of the University of California.  All rights reserved.
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
 *	@(#)extern.h	8.2 (Berkeley) 1/7/94
 * $FreeBSD: src/sbin/restore/extern.h,v 1.5 1999/08/28 00:14:05 peter Exp $
 * $DragonFly: src/sbin/restore/extern.h,v 1.4 2005/08/28 04:35:14 dillon Exp $
 */

struct entry	*addentry(char *, ufs1_ino_t, int);
long		 addfile(char *, ufs1_ino_t, int);
int		 addwhiteout(char *);
void		 badentry(struct entry *, char *);
void	 	 canon(char *, char *, int);
void		 checkrestore(void);
void		 closemt(void);
void		 createfiles(void);
void		 createleaves(char *);
void		 createlinks(void);
long		 deletefile(char *, ufs1_ino_t, int);
void		 deleteino(ufs1_ino_t);
void		 delwhiteout(struct entry *);
ufs1_ino_t	 dirlookup(const char *);
void 	 	 done(int) __dead2;
void		 dumpsymtable(char *, long);
void	 	 extractdirs(int);
int		 extractfile(char *);
void		 findunreflinks(void);
char		*flagvalues(struct entry *);
void		 freeentry(struct entry *);
void		 freename(char *);
int	 	 genliteraldir(char *, ufs1_ino_t);
char		*gentempname(struct entry *);
void		 getfile(void (*)(char *, long), void (*)(char *, long));
void		 getvol(long);
void		 initsymtable(char *);
int	 	 inodetype(ufs1_ino_t);
int		 linkit(char *, char *, int);
struct entry	*lookupino(ufs1_ino_t);
struct entry	*lookupname(char *);
long		 listfile(char *, ufs1_ino_t, int);
ufs1_ino_t	 lowerbnd(ufs1_ino_t);
void		 mktempname(struct entry *);
void		 moveentry(struct entry *, char *);
void		 msg(const char *, ...) __printflike(1, 2);
char		*myname(struct entry *);
void		 newnode(struct entry *);
void		 newtapebuf(long);
long		 nodeupdates(char *, ufs1_ino_t, int);
void	 	 onintr(int);
void		 panic(const char *, ...) __printflike(1, 2);
void		 pathcheck(char *);
struct direct	*pathsearch(const char *);
void		 printdumpinfo(void);
void		 removeleaf(struct entry *);
void		 removenode(struct entry *);
void		 removeoldleaves(void);
void		 removeoldnodes(void);
void		 renameit(char *, char *);
int		 reply(char *);
RST_DIR		*rst_opendir(const char *);
struct direct	*rst_readdir(RST_DIR *);
void		 rst_closedir(RST_DIR *dirp);
void	 	 runcmdshell(void);
char		*savename(char *);
void	 	 setdirmodes(int);
void		 setinput(char *);
void		 setup(void);
void	 	 skipdirs(void);
void		 skipfile(void);
void		 skipmaps(void);
void		 swabst(u_char *, u_char *);
void	 	 treescan(char *, ufs1_ino_t, long (*)(char *, ufs1_ino_t, int));
ufs1_ino_t	 upperbnd(ufs1_ino_t);
long		 verifyfile(char *, ufs1_ino_t, int);
void		 xtrnull(char *, long);

/* From ../dump/dumprmt.c */
void		rmtclose(void);
int		rmthost(char *);
int		rmtioctl(int, int);
int		rmtopen(char *, int);
int		rmtread(char *, int);
int		rmtseek(int, int);
