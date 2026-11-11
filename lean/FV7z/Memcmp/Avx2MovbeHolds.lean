import FV7z.Memcmp.Avx2Movbe.Entry
/-!
# The theorem of `checks/memcmp-avx2-movbe` (PLAN.md G2.1)

Under the name and statement of `Challenges/V2606/MemcmpAvx2Movbe.lean`: the bytes the file holds at `0x63f660` are
`avx2Movbe` (`avx2Movbe_pin`), which implement `memcmp` (`avx2Movbe_holds`).
-/
namespace FV7z.V2606
open ZellicX86

theorem memcmpAvx2Movbe_holds : ∀ code, Exe.bytesAt zzs.blob 0x63f660 980 = some code →
    ∀ (L : List (Addr × List Byte)) (prof : Profile) (e : Addr), prof.feat.avx = true → prof.feat.avx2 = true →
      prof.feat.movbe = true → CodeIn L e code → ImplementsCall prof e L Memcmp.contract := by
  intro code hc L prof e h1 h2 h3 hin
  rw [MemcmpAvx2.avx2Movbe_pin] at hc
  obtain rfl := Option.some.inj hc
  exact MemcmpAvx2.avx2Movbe_holds L prof e ⟨h1, h2, h3⟩ hin

end FV7z.V2606
