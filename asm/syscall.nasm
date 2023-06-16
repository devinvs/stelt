section .text
    global syscall0
    global syscall1
    global syscall2
    global syscall3
    global syscall4

syscall0:
    mov rax, rdi
    syscall
    ret

syscall1:
    mov rax, rdi
    mov rdi, rsi
    syscall
    ret

syscall2:
    mov rax, rdi
    mov rdi, rsi
    mov rsi, rdx
    syscall
    ret

syscall3:
    mov rax, rdi
    mov rdi, rsi
    mov rsi, rdx,
    mov rdx, r8
    syscall
    ret

syscall4:
    mov rax, rdi
    mov rdi, rsi
    mov rsi, rdx
    mov rdx, r8
    mov r8, r9
    syscall
    ret
