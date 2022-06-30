.section .text


.global myfunc
.global run_in_umode



utext_start:

// int myfunc(void);
myfunc:
	// Set return value to 42
	addi	a0, x0, 42

	// Return to caller
	jalr	x0, 0(ra)

utext_end:


// void run_in_umode(int (*funptr)(void));
run_in_umode:
	// Zero "mstatus" to set MPP=umode (note: shouldve bitmasked)
	addi	t0, x0, 0
	//TODO csrrw   x0, mstatus, t0

	// Set "mepc" to the func ptr in arg 0
	csrrw	x0, mepc, a0

	// mret to func ptr in arg 0, instead of returning to caller
	mret
