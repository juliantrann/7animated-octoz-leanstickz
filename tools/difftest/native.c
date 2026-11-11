// The processor's side of the differential test (PLAN.md §6.4, G1); lean/Tools/DiffTest.lean is the model's side and
// documents the case format. Each case's instruction runs natively in a stub built on an executable page:
//   rdi = &ctx; load YMM0-YMM7, rax (buffer + offset), rcx, rdx, RFLAGS from ctx; the instruction; store them back.
// The instruction may use only rax, rcx, rdx, YMM0-YMM7, and memory at [rax + disp]: the generator sees to it.
// SIGSEGV is reported as `gp` (si_code SI_KERNEL: #GP) or `pf` (a page fault), SIGILL as `ud`, SIGBUS as `ac`.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

struct ctx { uint8_t ymm[8][32]; uint64_t rax, rflags_in, rflags_out, rcx, rdx; };   // offsets 0, 256, 264, 272, 280, 288

static sigjmp_buf jb;
static volatile int sig, scode;
static void handler(int s, siginfo_t *si, void *uc) { (void)uc; sig = s; scode = si->si_code; siglongjmp(jb, 1); }

static int hex(int c) { return c <= '9' ? c - '0' : (c | 32) - 'a' + 10; }
static void parse(const char *s, uint8_t *out, size_t n) { for (size_t i = 0; i < n; i++) out[i] = hex(s[2*i]) << 4 | hex(s[2*i+1]); }
static uint64_t u64(const char *s) { return strtoull(s, 0, 16); }
static uint8_t *emit(uint8_t *p, const char *b, size_t n) { memcpy(p, b, n); return p + n; }
static uint8_t *disp32(uint8_t *p, uint32_t d) { memcpy(p, &d, 4); return p + 4; }

int main(void) {
  // the buffer: the last 64 bytes of a page whose successor is unmapped, so an access past its end faults as the
  // model's does (the generator gives no negative offsets, before the buffer, where the model faults and this not)
  uint8_t *region = mmap(0, 3 * 4096, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  mprotect(region + 4096, 4096, PROT_READ | PROT_WRITE);
  uint8_t *buf = region + 2 * 4096 - 64;
  uint8_t *code = mmap(0, 4096, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  struct sigaction sa = {0}; sa.sa_sigaction = handler; sa.sa_flags = SA_SIGINFO | SA_NODEFER;
  sigaction(SIGSEGV, &sa, 0); sigaction(SIGILL, &sa, 0); sigaction(SIGBUS, &sa, 0);
  char line[4096];
  while (fgets(line, sizeof line, stdin)) {
    char *f[16]; int n = 0;
    for (char *t = strtok(line, " \n"); t && n < 16; t = strtok(0, " \n")) f[n++] = t;
    if (n < 14) { puts("bad"); continue; }
    struct ctx c; memset(&c, 0, sizeof c);
    for (int i = 0; i < 8; i++) {   // most significant first in the case; little-endian in the register
      uint8_t be[32]; parse(f[5 + i], be, 32);
      for (int j = 0; j < 32; j++) c.ymm[i][j] = be[31 - j];
    }
    parse(f[13], buf, 64);
    c.rax = (uint64_t)buf + u64(f[1]); c.rcx = u64(f[2]); c.rdx = u64(f[3]);
    c.rflags_in = (u64(f[4]) & 0x8d5) | 0x202;
    uint8_t *p = code; size_t ilen = strlen(f[0]) / 2;
    for (int i = 0; i < 8; i++) { p = emit(p, "\xc5\xfe\x6f", 3); *p++ = 0x87 | i << 3; p = disp32(p, 32 * i); }   // vmovdqu ymmi,[rdi+32i]
    p = emit(p, "\x48\x8b\x87\x00\x01\x00\x00", 7);                  // mov rax,[rdi+256]
    p = emit(p, "\x48\x8b\x8f\x18\x01\x00\x00", 7);                  // mov rcx,[rdi+280]
    p = emit(p, "\x48\x8b\x97\x20\x01\x00\x00", 7);                  // mov rdx,[rdi+288]
    p = emit(p, "\xff\xb7\x08\x01\x00\x00\x9d", 7);                  // push qword [rdi+264]; popfq
    parse(f[0], p, ilen); p += ilen;                                  // the instruction
    p = emit(p, "\x9c\x8f\x87\x10\x01\x00\x00", 7);                  // pushfq; pop qword [rdi+272]
    p = emit(p, "\x48\x89\x8f\x18\x01\x00\x00", 7);                  // mov [rdi+280],rcx
    p = emit(p, "\x48\x89\x97\x20\x01\x00\x00", 7);                  // mov [rdi+288],rdx
    for (int i = 0; i < 8; i++) { p = emit(p, "\xc5\xfe\x7f", 3); *p++ = 0x87 | i << 3; p = disp32(p, 32 * i); }   // vmovdqu [rdi+32i],ymmi
    p = emit(p, "\xc5\xf8\x77\xc3", 4);                               // vzeroupper; ret
    sig = 0;
    if (sigsetjmp(jb, 1) == 0) {
      ((void (*)(struct ctx *))code)(&c);
    }
    if (sig == SIGSEGV) { printf("exc %s\n", scode == SI_KERNEL ? "gp" : "pf"); continue; }
    if (sig == SIGILL) { puts("exc ud"); continue; }
    if (sig == SIGBUS) { puts("exc ac"); continue; }
    printf("ok %03llx %016llx %016llx", (unsigned long long)(c.rflags_out & 0x8d5), (unsigned long long)c.rcx,
           (unsigned long long)c.rdx);
    for (int i = 0; i < 8; i++) { putchar(' '); for (int j = 31; j >= 0; j--) printf("%02x", c.ymm[i][j]); }
    putchar(' '); for (int i = 0; i < 64; i++) printf("%02x", buf[i]);
    putchar('\n');
  }
  return 0;
}
