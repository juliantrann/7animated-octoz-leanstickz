import ZellicX86.Spec.Statement
/-!
# The kernel's version as `_dl_discover_osversion` reads it (PLAN.md G3, startup)

Only definitions, on Zellic's model alone.

glibc 2.31's `_dl_discover_osversion` (`sysdeps/unix/sysv/linux/dl-sysdep.c`) makes a number of the release that
`uname` gives (`struct new_utsname`'s third field, 65 bytes from offset 130): at most three numbers in decimal, with
a `.` between two, each `unsigned int` (so modulo `2 ^ 32`), the first in the bits from 16, the second from 8, the
third from 0; with fewer than three, the bits are as if the missing ones were 0. `__libc_start_main` stops the
program (`__libc_fatal`, "kernel too old") unless the number, as an `int`, is above `0x301ff`: Linux 3.2.0, what this
glibc was built for (`__LINUX_KERNEL_VERSION`), or later.

- `osVersion u`: the number, of the bytes `u` of a `struct new_utsname`.
- `KernelNew u`: it is above `0x301ff`.
-/
namespace FV7z
open ZellicX86

/-- A decimal digit. -/
def isDig (c : Byte) : Bool := decide (48 ≤ c.toNat ∧ c.toNat ≤ 57)

/-- The number `here` continued with the digits a string starts with, and the rest of the string. -/
def osNum (here : BitVec 32) : List Byte → BitVec 32 × List Byte
  | [] => (here, [])
  | c :: cs => if isDig c then osNum (here * 10 + (c.setWidth 32 - 48)) cs else (here, c :: cs)

/-- After a number `here`, `left` more to read after it, the version so far `ver`: with a `.` next the reading goes
on (`k`), otherwise the missing numbers are 0. -/
def osTail (k : BitVec 32 → List Byte → BitVec 32) (left : Nat) (ver here : BitVec 32) : List Byte → BitVec 32
  | [] => (ver <<< 8 ||| here) <<< (8 * left)
  | c :: cs => if c = 46 then k (ver <<< 8 ||| here) cs else (ver <<< 8 ||| here) <<< (8 * left)

/-- The version of at most `left` more numbers of a string, after the version so far `ver`. -/
def osParts : Nat → BitVec 32 → List Byte → BitVec 32
  | 0, ver, _ => ver
  | left + 1, ver, [] => ver <<< (8 * (left + 1))
  | left + 1, ver, c :: cs =>
    if isDig c then
      osTail (osParts left) left ver (osNum (c.setWidth 32 - 48) cs).1 (osNum (c.setWidth 32 - 48) cs).2
    else ver <<< (8 * (left + 1))

/-- The release of the bytes `u` of a `struct new_utsname`: its third field. -/
def release (u : List Byte) : List Byte := (u.drop 130).take 65

/-- The kernel's version as `_dl_discover_osversion` reads it in the bytes `u` of a `struct new_utsname`. -/
def osVersion (u : List Byte) : BitVec 32 := osParts 3 0 (release u)

/-- The release in `u` is of a kernel that glibc 2.31 as built in `7zzs` runs on: Linux 3.2.0 or later. -/
def KernelNew (u : List Byte) : Prop := 0x301ff < (osVersion u).toInt

/-- `6.18.35-…` is read as `0x061223`. -/
example : osParts 3 0 [54, 46, 49, 56, 46, 51, 53, 45, 0] = 0x061223#32 := by decide

/-- `3.2` is read as `0x030200`. -/
example : osParts 3 0 [51, 46, 50, 0] = 0x030200#32 := by decide

end FV7z
