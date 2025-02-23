#include <stdint.h>

// TODO: reimplement this using biased reference counting

void rc_init(uint64_t *ptr) {
    *ptr = 1;
}

void rc_inc(_Atomic(uint64_t) *ptr) {
    *ptr += 1;
}

void rc_dec(_Atomic(uint64_t) *ptr, void (*dealloc)(void *)) {
    if (*ptr == 1) {
        dealloc(ptr);
    } else {
        *ptr -= 1;
    }
}
