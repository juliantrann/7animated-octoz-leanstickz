// What FCW reads back (FNSTCW) after FLDCW, FLDENV, FRSTOR, FXRSTOR and XRSTOR load each 16-bit value, with FSW clear
// (no exception pending). Compares with the model's `x87Fcw` (Spec/Xsave.lean): (v & 0x1F3F) | 0x40.
// Then what FSW reads back (FNSTSW) after FLDENV, FRSTOR, FXRSTOR and XRSTOR load each 16-bit FSW with FCW 037FH (all
// exceptions masked) and 0340H (all unmasked), against the model's `x87Summary` (ES and B recomputed).
// Output: per load, the number of values that differ, then the first few differing values.
// The XSAVE images get XSTATE_BV[0] set before XRSTOR: after FNINIT an AMD processor's XSAVE leaves it clear (x87 in its
// initial configuration, XINUSE[0] = 0), and XRSTOR would then initialize x87 rather than load the image.
#include <stdint.h>
#include <stdio.h>
#include <string.h>
static unsigned total;   // differing values over every load: the exit status is 1 if any
static uint16_t model(uint16_t v) { return (v & 0x1F3F) | 0x40; }
static uint16_t stcw(void) { uint16_t c; __asm__ volatile("fnstcw %0" : "=m"(c)); return c; }
static uint8_t env[28] __attribute__((aligned(16)));
static uint8_t sv[108] __attribute__((aligned(16)));
static uint8_t fx[512] __attribute__((aligned(64)));
static uint8_t xs[4096] __attribute__((aligned(64)));
static uint16_t summary(uint16_t fcw, uint16_t fsw) {
  int es = (fsw & ~fcw & 0x3F) != 0; return (fsw & ~0x8080) | (es ? 0x8080 : 0); }
static uint16_t stsw(void) { uint16_t c; __asm__ volatile("fnstsw %0" : "=m"(c)); return c; }
static uint16_t loadsw(int k, uint16_t fcw, uint16_t v) {
  __asm__ volatile("fninit");
  switch (k) {
  case 1: __asm__ volatile("fnstenv %0" : "=m"(env)); memcpy(env, &fcw, 2); memcpy(env + 4, &v, 2);
          __asm__ volatile("fldenv %0" :: "m"(env)); break;
  case 4: __asm__ volatile("fnsave %0" : "=m"(sv)); memcpy(sv, &fcw, 2); memcpy(sv + 4, &v, 2);
          __asm__ volatile("frstor %0" :: "m"(sv)); break;
  case 2: __asm__ volatile("fxsave %0" : "=m"(fx)); memcpy(fx, &fcw, 2); memcpy(fx + 2, &v, 2);
          __asm__ volatile("fxrstor %0" :: "m"(fx)); break;
  case 3: memset(xs, 0, sizeof xs); __asm__ volatile("xsave %0" : "=m"(xs) : "a"(1), "d"(0));
          memcpy(xs, &fcw, 2); memcpy(xs + 2, &v, 2); xs[512] |= 1; __asm__ volatile("xrstor %0" :: "m"(xs), "a"(1), "d"(0)); break;
  }
  uint16_t c = stsw(); __asm__ volatile("fninit"); return c;
}
static uint16_t load(int k, uint16_t v) {
  __asm__ volatile("fninit");
  switch (k) {
  case 0: __asm__ volatile("fldcw %0" :: "m"(v)); break;
  case 1: __asm__ volatile("fnstenv %0" : "=m"(env)); memcpy(env, &v, 2); __asm__ volatile("fldenv %0" :: "m"(env)); break;
  case 4: __asm__ volatile("fnsave %0" : "=m"(sv)); memcpy(sv, &v, 2); __asm__ volatile("frstor %0" :: "m"(sv)); break;
  case 2: __asm__ volatile("fxsave %0" : "=m"(fx)); memcpy(fx, &v, 2); __asm__ volatile("fxrstor %0" :: "m"(fx)); break;
  case 3: memset(xs, 0, sizeof xs); __asm__ volatile("xsave %0" : "=m"(xs) : "a"(1), "d"(0));
          memcpy(xs, &v, 2); xs[512] |= 1; __asm__ volatile("xrstor %0" :: "m"(xs), "a"(1), "d"(0)); break;
  }
  uint16_t c = stcw(); __asm__ volatile("fninit"); return c;
}
int main(void) {
  const char *name[] = {"fldcw", "fldenv", "fxrstor", "xrstor", "frstor"};
  for (int k = 0; k < 5; k++) {
    unsigned bad = 0; unsigned ex[4][2]; int ne = 0;
    for (unsigned v = 0; v < 65536; v++) {
      uint16_t c = load(k, v);
      if (c != model(v)) { if (ne < 4) { ex[ne][0] = v; ex[ne][1] = c; ne++; } bad++; total++; }
    }
    printf("%s: %u of 65536 differ from x87Fcw", name[k], bad);
    for (int i = 0; i < ne; i++) printf("  %04x->%04x(model %04x)", ex[i][0], ex[i][1], model(ex[i][0]));
    printf("\n");
  }
  for (int k = 1; k < 5; k++)
    for (int m = 0; m < 2; m++) {
      uint16_t fcw = m ? 0x0340 : 0x037F; unsigned bad = 0; unsigned ex[4][2]; int ne = 0;
      for (unsigned v = 0; v < 65536; v++) {
        uint16_t c = loadsw(k, fcw, v);
        if (c != summary(fcw, v)) { if (ne < 4) { ex[ne][0] = v; ex[ne][1] = c; ne++; } bad++; total++; }
      }
      printf("%s fsw (fcw %04x): %u of 65536 differ from x87Summary", name[k], fcw, bad);
      for (int i = 0; i < ne; i++) printf("  %04x->%04x(model %04x)", ex[i][0], ex[i][1], summary(fcw, ex[i][0]));
      printf("\n");
    }
  return total != 0;
}
