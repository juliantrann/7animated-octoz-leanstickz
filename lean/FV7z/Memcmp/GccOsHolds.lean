import FV7z.Memcmp.GccOs
/-!
# Zellic's release challenge `memcmp_gcc_os`, by this project's proof (PLAN.md G2.0)

The theorem under the name and statement of `ReleaseChallenges/memcmp_gcc_os.lean` (`refs/zellic-x86`), for
`tools/check.sh memcmp-gcc-os`: `lake comparator` holds it to exactly that statement.
-/

theorem Memcmp.gccOs_holds : Memcmp.holds Memcmp.gccOs := FV7z.MemcmpGccOs.gccOs_holds
