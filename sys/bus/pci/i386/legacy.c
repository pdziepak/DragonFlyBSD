/*-
 * Copyright 1998 Massachusetts Institute of Technology
 *
 * Permission to use, copy, modify, and distribute this software and
 * its documentation for any purpose and without fee is hereby
 * granted, provided that both the above copyright notice and this
 * permission notice appear in all copies, that both the above
 * copyright notice and this permission notice appear in all
 * supporting documentation, and that the name of M.I.T. not be used
 * in advertising or publicity pertaining to distribution of the
 * software without specific, written prior permission.  M.I.T. makes
 * no representations about the suitability of this software for any
 * purpose.  It is provided "as is" without express or implied
 * warranty.
 *
 * THIS SOFTWARE IS PROVIDED BY M.I.T. ``AS IS''.  M.I.T. DISCLAIMS
 * ALL EXPRESS OR IMPLIED WARRANTIES WITH REGARD TO THIS SOFTWARE,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. IN NO EVENT
 * SHALL M.I.T. BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 * __FBSDID("$FreeBSD: src/sys/i386/i386/legacy.c,v 1.63.2.1.4.1 2009/04/15 03:14:26 kensmith Exp $");
 */

#include <sys/cdefs.h>

/*
 * This code implements a system driver for legacy systems that do not
 * support ACPI or when ACPI support is not present in the kernel.
 */

#include <sys/param.h>
#include <sys/systm.h>
#include <sys/bus.h>
#include <sys/kernel.h>
#include <sys/malloc.h>
#include <sys/module.h>
#include <sys/rman.h>

#undef DEV_MCA
#ifdef DEV_MCA
#include <i386/bios/mca_machdep.h>
#endif

#include <machine/legacyvar.h>

static MALLOC_DEFINE(M_LEGACYDEV, "legacydrv", "legacy system device");
struct legacy_device {
	int			lg_pcibus;
};

#define DEVTOAT(dev)	((struct legacy_device *)device_get_ivars(dev))

static int	legacy_identify(driver_t *, device_t);
static int	legacy_probe(device_t);
static int	legacy_attach(device_t);
static int	legacy_print_child(device_t, device_t);
static device_t	legacy_add_child(device_t, device_t, int, const char *, int);
static int	legacy_read_ivar(device_t, device_t, int, uintptr_t *);
static int	legacy_write_ivar(device_t, device_t, int, uintptr_t);

static device_method_t legacy_methods[] = {
	/* Device interface */
	DEVMETHOD(device_identify,	legacy_identify),
	DEVMETHOD(device_probe,		legacy_probe),
	DEVMETHOD(device_attach,	legacy_attach),
	DEVMETHOD(device_detach,	bus_generic_detach),
	DEVMETHOD(device_shutdown,	bus_generic_shutdown),
	DEVMETHOD(device_suspend,	bus_generic_suspend),
	DEVMETHOD(device_resume,	bus_generic_resume),

	/* Bus interface */
	DEVMETHOD(bus_print_child,	legacy_print_child),
	DEVMETHOD(bus_add_child,	legacy_add_child),
	DEVMETHOD(bus_read_ivar,	legacy_read_ivar),
	DEVMETHOD(bus_write_ivar,	legacy_write_ivar),
	DEVMETHOD(bus_alloc_resource,	bus_generic_alloc_resource),
	DEVMETHOD(bus_release_resource,	bus_generic_release_resource),
	DEVMETHOD(bus_activate_resource, bus_generic_activate_resource),
	DEVMETHOD(bus_deactivate_resource, bus_generic_deactivate_resource),
	DEVMETHOD(bus_setup_intr,	bus_generic_setup_intr),
	DEVMETHOD(bus_teardown_intr,	bus_generic_teardown_intr),

	{ 0, 0 }
};

static driver_t legacy_driver = {
	"legacy",
	legacy_methods,
	1,			/* no softc */
};
static devclass_t legacy_devclass;

DRIVER_MODULE(legacy, nexus, legacy_driver, legacy_devclass, 0, 0);

static int
legacy_identify(driver_t *driver, device_t parent)
{
	/*
	 * Basically a static device, there's no point reinstalling it
	 * on rescan.
	 */
	if (device_get_state(parent) == DS_ATTACHED)
		return (0);
	if (device_get_state(parent) == DS_INPROGRESS)
		return (0);

	/*
	 * Add child device with order of 11 so it gets probed
	 * after ACPI (which is at order 10).
	 */
	if (BUS_ADD_CHILD(parent, parent, 11, "legacy", 0) == NULL)
		panic("legacy: could not attach");
	return (0);
}

static int
legacy_probe(device_t dev)
{
#ifdef ACPI_ENABLE_PCI
	device_t acpi;

	/*
	 * Fail to probe if ACPI is ok.
	 */
	acpi = devclass_get_device(devclass_find("acpi"), 0);
	if (acpi != NULL && device_is_alive(acpi))
		return (ENXIO);
#endif	/* ACPI_ENABLE_PCI */
	device_set_desc(dev, "legacy system");
	device_quiet(dev);
	return (0);
}

static int
legacy_attach(device_t dev)
{
	device_t child;

	/*
	 * Let our child drivers identify any child devices that they
	 * can find.  Once that is done attach any devices that we
	 * found.
	 */
	bus_generic_probe(dev);
	bus_generic_attach(dev);

#ifndef PC98
	/*
	 * If we didn't see EISA or ISA on a pci bridge, create some
	 * connection points now so they show up "on motherboard".
	 */
	if (!devclass_get_device(devclass_find("eisa"), 0)) {
		child = BUS_ADD_CHILD(dev, dev, 0, "eisa", 0);
		if (child == NULL)
			panic("legacy_attach eisa");
		device_probe_and_attach(child);
	}
#endif
#ifdef DEV_MCA
	if (MCA_system && !devclass_get_device(devclass_find("mca"), 0)) {
		child = BUS_ADD_CHILD(dev, dev, 0, "mca", 0);
		if (child == 0)
			panic("legacy_probe mca");
		device_probe_and_attach(child);
	}
#endif
	if (!devclass_get_device(devclass_find("isa"), 0)) {
		child = BUS_ADD_CHILD(dev, dev, 0, "isa", 0);
		if (child == NULL)
			panic("legacy_attach isa");
		device_probe_and_attach(child);
	}

	return 0;
}

static int
legacy_print_child(device_t bus, device_t child)
{
	struct legacy_device *atdev = DEVTOAT(child);
	int retval = 0;

	retval += bus_print_child_header(bus, child);
	if (atdev->lg_pcibus != -1)
		retval += kprintf(" pcibus %d", atdev->lg_pcibus);
	retval += kprintf(" on motherboard\n");	/* XXX "motherboard", ick */

	return (retval);
}

static device_t
legacy_add_child(device_t bus, device_t parent, int order, const char *name, int unit)
{
	device_t child;
	struct legacy_device *atdev;
	atdev = kmalloc(sizeof(struct legacy_device), M_LEGACYDEV,
	    M_NOWAIT | M_ZERO);
	if (atdev == NULL)
		return(NULL);
	atdev->lg_pcibus = -1;

	child = device_add_child_ordered(bus, order, name, unit);
	if (child == NULL) {
		kfree(atdev, M_LEGACYDEV);
	}
	else {
		/* should we kfree this in legacy_child_detached? */
		device_set_ivars(child, atdev);
	}
	return (child);
}

static int
legacy_read_ivar(device_t dev, device_t child, int which, uintptr_t *result)
{
	struct legacy_device *atdev = DEVTOAT(child);

	switch (which) {
	case LEGACY_IVAR_PCIDOMAIN:
		*result = 0;
		break;
	case LEGACY_IVAR_PCIBUS:
		*result = atdev->lg_pcibus;
		break;
	default:
		return ENOENT;
	}
	return 0;
}

static int
legacy_write_ivar(device_t dev, device_t child, int which, uintptr_t value)
{
	struct legacy_device *atdev = DEVTOAT(child);

	switch (which) {
	case LEGACY_IVAR_PCIDOMAIN:
		return EINVAL;
	case LEGACY_IVAR_PCIBUS:
		atdev->lg_pcibus = value;
		break;
	default:
		return ENOENT;
	}
	return 0;
}

#ifdef notyet
/*
 * Legacy CPU attachment when ACPI is not available.  Drivers like
 * cpufreq(4) hang off this.
 */
static void	cpu_identify(driver_t *driver, device_t parent);
static int	cpu_read_ivar(device_t dev, device_t child, int index,
		    uintptr_t *result);
static device_t cpu_add_child(device_t bus, int order, const char *name,
		    int unit);
static struct resource_list *cpu_get_rlist(device_t dev, device_t child);

struct cpu_device {
	struct resource_list cd_rl;
	struct pcpu *cd_pcpu;
};

static device_method_t cpu_methods[] = {
	/* Device interface */
	DEVMETHOD(device_identify,	cpu_identify),
	DEVMETHOD(device_probe,		bus_generic_probe),
	DEVMETHOD(device_attach,	bus_generic_attach),
	DEVMETHOD(device_detach,	bus_generic_detach),
	DEVMETHOD(device_shutdown,	bus_generic_shutdown),
	DEVMETHOD(device_suspend,	bus_generic_suspend),
	DEVMETHOD(device_resume,	bus_generic_resume),

	/* Bus interface */
	DEVMETHOD(bus_add_child,	cpu_add_child),
	DEVMETHOD(bus_read_ivar,	cpu_read_ivar),
	DEVMETHOD(bus_print_child,	bus_generic_print_child),
	DEVMETHOD(bus_get_resource_list, cpu_get_rlist),
	DEVMETHOD(bus_get_resource,	bus_generic_rl_get_resource),
	DEVMETHOD(bus_set_resource,	bus_generic_rl_set_resource),
	DEVMETHOD(bus_alloc_resource,	bus_generic_rl_alloc_resource),
	DEVMETHOD(bus_release_resource,	bus_generic_rl_release_resource),
	DEVMETHOD(bus_driver_added,	bus_generic_driver_added),
	DEVMETHOD(bus_activate_resource, bus_generic_activate_resource),
	DEVMETHOD(bus_deactivate_resource, bus_generic_deactivate_resource),
	DEVMETHOD(bus_setup_intr,	bus_generic_setup_intr),
	DEVMETHOD(bus_teardown_intr,	bus_generic_teardown_intr),

	{ 0, 0 }
};

static driver_t cpu_driver = {
	"cpu",
	cpu_methods,
	1,		/* no softc */
};
static devclass_t cpu_devclass;
DRIVER_MODULE(cpu, legacy, cpu_driver, cpu_devclass, 0, 0);

static void
cpu_identify(driver_t *driver, device_t parent)
{
	device_t child;
	int i;

	/*
	 * Attach a cpuX device for each CPU.  We use an order of 150
	 * so that these devices are attached after the Host-PCI
	 * bridges (which are added at order 100).
	 */
	for (i = 0; i <= mp_maxid; i++)
		if (!CPU_ABSENT(i)) {
			child = BUS_ADD_CHILD(parent, 150, "cpu", i);
			if (child == NULL)
				panic("legacy_attach cpu");
		}
}

static device_t
cpu_add_child(device_t bus, int order, const char *name, int unit)
{
	struct cpu_device *cd;
	device_t child;
	struct pcpu *pc;

	if ((cd = kmalloc(sizeof(*cd), M_DEVBUF, M_NOWAIT | M_ZERO)) == NULL)
		return (NULL);

	resource_list_init(&cd->cd_rl);
	pc = pcpu_find(device_get_unit(bus));
	cd->cd_pcpu = pc;

	child = device_add_child_ordered(bus, order, name, unit);
	if (child != NULL) {
		pc->pc_device = child;
		device_set_ivars(child, cd);
	} else
		kfree(cd, M_DEVBUF);
	return (child);
}

static struct resource_list *
cpu_get_rlist(device_t dev, device_t child)
{
	struct cpu_device *cpdev;

	cpdev = device_get_ivars(child);
	return (&cpdev->cd_rl);
}

static int
cpu_read_ivar(device_t dev, device_t child, int index, uintptr_t *result)
{
	struct cpu_device *cpdev;

	if (index != CPU_IVAR_PCPU)
		return (ENOENT);
	cpdev = device_get_ivars(child);
	*result = (uintptr_t)cpdev->cd_pcpu;
	return (0);
}
#endif
