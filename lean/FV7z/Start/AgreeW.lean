import FV7z.Start.PlEnt
/-!
# Words of the memory at `0x613434` in `launch_to_ptr`'s bytes (PLAN.md G3, startup)

`launch_to_ptr` hands on the memory of the state at the `call` of `__libc_init_first` and bytes `W` that agree with
it on the data footprint. Facts it states of the memory (`CpuFeat.HwW`, the word `_dl_platform` that
`CpuFeat.PlW` is about) hold of `W` where the footprint holds their bytes.

- `agree_rdq`: 8 bytes of the footprint read the same in the memory and in `W`.
- `agree_hw`: `HwW` of the memory gives `HwW W`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

theorem agree_rdq {F : Footprint} {m : Memory} {W : Addr → Byte} {x : Addr} (hA : Agree F m W)
    (h : ∀ i < 8, Foot F.data (x.add i)) : rdq(m.readByte, x) = rdq(W, x) :=
  congrArg (ofBytesLE 64) (hA.read h)

theorem agree_hw {F : Footprint} {m : Memory} {W : Addr → Byte} (hA : Agree F m W)
    (h : ∀ i < 8, Foot F.data ((0x7a4ac8 : Addr).add i)) (hw : CpuFeat.HwW m.readByte) : CpuFeat.HwW W := by
  unfold CpuFeat.HwW at hw ⊢
  rw [← agree_rdq hA h]
  exact hw

end FV7z.Start
