.section .text


.global myfunc
.global run_in_umode
.global setup_pmp
.global set_mmode


utext_start:

// int myfunc(void)
myfunc:
	// Set return value to 42
	addi	a0, x0, 42

	// Return to caller
	jalr	x0, 0(ra)

utext_end:


// void run_in_umode(int (*funptr)(void))
run_in_umode:
	// Zero "mstatus" to set MPP=umode (note: shouldve bitmasked)
	addi	t0, x0, 0
	csrrw   x0, mstatus, t0

	// Set "mepc" to the func ptr in arg 0
	csrrw	x0, mepc, a0

	// mret to func ptr in arg 0, instead of returning to caller
	mret


// void setup_pmp(void)
setup_pmp:
	// Set pmp addr to 0xFFFF_FFFF
	li	t0, 0xFFFFFFFF
	csrrw	x0, pmpaddr0, t0

	// Set pmp region TOR and executable
	li	t0, ((1 << 3) + (1 << 2))
	csrrw	x0, pmpcfg0, t0

	// Return to caller
	jalr	x0, 0(ra)


// extern volatile void set_mmode(void)
set_mmode:
	// Set "mstatus.MPP" to M-mode (note: shouldve bitmasked)
	li	t0, (3 << 11)
	csrrw   x0, mstatus, t0

	// Set "mepc" to the link register
	csrrw	x0, mepc, a0

	// Return with mret instead of jalr
	mret
