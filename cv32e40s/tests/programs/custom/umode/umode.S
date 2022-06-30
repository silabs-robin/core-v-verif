.section .text

.global myfunc

myfunc:
	addi	a0, x0, 42
	jalr	x0, 0(ra)
