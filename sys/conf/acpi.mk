# $DragonFly: src/sys/conf/acpi.mk,v 1.1 2005/08/16 10:31:35 y0netan1 Exp $
#

ACPICA_VERSION=		20050309
ACPICA_DIR?=		contrib/dev/acpica-unix-${ACPICA_VERSION}
OSACPI_MI_DIR?=		dev/acpica5
OSACPI_MD_DIR?=		${MACHINE_ARCH}/acpica5

.if !defined(SYSDIR) && defined(S)
SYSDIR=	$S
.endif

.PATH:	${SYSDIR}/${ACPICA_DIR}/interpreter/dispatcher 	\
	${SYSDIR}/${ACPICA_DIR}/interpreter/executer	\
	${SYSDIR}/${ACPICA_DIR}/interpreter/parser	\
	${SYSDIR}/${ACPICA_DIR}/events			\
	${SYSDIR}/${ACPICA_DIR}/hardware		\
	${SYSDIR}/${ACPICA_DIR}/namespace		\
	${SYSDIR}/${ACPICA_DIR}/resources		\
	${SYSDIR}/${ACPICA_DIR}/tables			\
	${SYSDIR}/${ACPICA_DIR}/utilities		\
	${SYSDIR}/${ACPICA_DIR}/debugger		\
	${SYSDIR}/${ACPICA_DIR}/disassembler		\
	${SYSDIR}/${ACPICA_DIR}/INTERPRETER/DISPATCHER 	\
	${SYSDIR}/${ACPICA_DIR}/INTERPRETER/EXECUTER	\
	${SYSDIR}/${ACPICA_DIR}/INTERPRETER/PARSER	\
	${SYSDIR}/${ACPICA_DIR}/EVENTS			\
	${SYSDIR}/${ACPICA_DIR}/HARDWARE		\
	${SYSDIR}/${ACPICA_DIR}/NAMESPACE		\
	${SYSDIR}/${ACPICA_DIR}/RESOURCES		\
	${SYSDIR}/${ACPICA_DIR}/TABLES			\
	${SYSDIR}/${ACPICA_DIR}/UTILITIES

${.OBJDIR}/acpi.h: ${SYSDIR}/${ACPICA_DIR}/include/acpi.h
	cp ${.ALLSRC} ${.TARGET}

${.OBJDIR}/platform/acenv.h: ${SYSDIR}/${ACPICA_DIR}/include/platform/acenv.h
	mkdir -p ${.OBJDIR}/platform
	sed -e 's/__FreeBSD__/__DragonFly__/' \
	    -e 's/acfreebsd.h/acdragonfly.h/' ${.ALLSRC} > ${.TARGET}.new
	mv -f ${.TARGET}.new ${.TARGET}
