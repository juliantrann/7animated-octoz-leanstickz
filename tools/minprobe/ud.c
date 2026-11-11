/* PLAN.md §7, G1, H-CPU-min: the control of tools/mintrace.sh. `ud N` executes the N-th instruction of an optional
 * extension below and exits 0; on a processor without the extension it dies of SIGILL. Run natively it shows which the
 * host has; run under the emulator with the baseline processor it shows that the emulator raises #UD for each, so
 * that a run of 7zzs that does not die of SIGILL there executed none of them. `ud` alone prints the count. */
#include <stdio.h>
#include <stdlib.h>
static unsigned char buf[64] __attribute__((aligned(64)));
int main(int argc, char **argv) {
  static const char *names[] = {"lddqu (SSE3)", "pshufb (SSSE3)", "ptest (SSE4.1)", "pcmpistri (SSE4.2)",
                                "popcnt (POPCNT)", "vzeroupper (AVX)", "vpand ymm (AVX2)", "aesenc (AES)",
                                "sha1rnds4 (SHA)", "movbe (MOVBE)"};
  int n = sizeof names / sizeof *names;
  if (argc < 2) { printf("%d\n", n); return 0; }
  int i = atoi(argv[1]);
  if (i < 0 || i >= n) return 2;
  printf("%s\n", names[i]); fflush(stdout);
  switch (i) {
  case 0: __asm__ volatile(".byte 0xf2,0x0f,0xf0,0x07" :: "D"(buf) : "xmm0", "memory"); break;      /* lddqu xmm0,[rdi] */
  case 1: __asm__ volatile(".byte 0x66,0x0f,0x38,0x00,0xc1" ::: "xmm0"); break;                    /* pshufb xmm0,xmm1 */
  case 2: __asm__ volatile(".byte 0x66,0x0f,0x38,0x17,0xc1" ::: "cc"); break;                      /* ptest xmm0,xmm1 */
  case 3: __asm__ volatile(".byte 0x66,0x0f,0x3a,0x63,0xc1,0x00" ::: "rcx", "cc"); break;          /* pcmpistri xmm0,xmm1,0 */
  case 4: __asm__ volatile(".byte 0xf3,0x48,0x0f,0xb8,0xc0" ::: "rax", "cc"); break;               /* popcnt rax,rax */
  case 5: __asm__ volatile(".byte 0xc5,0xf8,0x77"); break;                                         /* vzeroupper */
  case 6: __asm__ volatile(".byte 0xc5,0xfd,0xdb,0xc1" ::: "xmm0"); break;                         /* vpand ymm0,ymm0,ymm1 */
  case 7: __asm__ volatile(".byte 0x66,0x0f,0x38,0xdc,0xc1" ::: "xmm0"); break;                    /* aesenc xmm0,xmm1 */
  case 8: __asm__ volatile(".byte 0x0f,0x3a,0xcc,0xc1,0x00" ::: "xmm0"); break;                    /* sha1rnds4 xmm0,xmm1,0 */
  case 9: __asm__ volatile(".byte 0x48,0x0f,0x38,0xf0,0x07" :: "D"(buf) : "rax", "memory"); break; /* movbe rax,[rdi] */
  }
  return 0;
}
