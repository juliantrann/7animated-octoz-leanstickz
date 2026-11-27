/-
Weakest preconditions of the cut points of `_nl_intern_locale_data`, as printed by `trace_state` after `wpx`
(triage kt536, run 45838651515; not built). The probe (removed) was, for each cut point `c` below:

  example {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} : Ild.W_c fb F Wl Q g f V := by
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    wpx [Ild.W_c, its pieces W_* and o*, Op.ldsx, Op.lea, Op.cmpmi, Op.sxr, Op.cmpm, Op.stfi, Op.cmov32]
    trace_state
    sorry

Lines are wrapped at 120 columns.

=== cut 0
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ (∀ (i : Nat), i < 8 → Foot Wl (Addr.add (rsp - 8) i)) ∧
    (∀ (i : Nat), i < 8 → Foot Wl (Addr.add (rsp - 8 - 8) i)) ∧
      (∀ (i : Nat), i < 8 → Foot Wl (Addr.add (rsp - 8 - 8 - 8) i)) ∧
        (∀ (i : Nat), i < 8 → Foot Wl (Addr.add (rsp - 8 - 8 - 8 - 8) i)) ∧
          (∀ (i : Nat), i < 8 → Foot Wl (Addr.add (rsp - 8 - 8 - 8 - 8 - 8) i)) ∧
            (∀ (i : Nat), i < 8 → Foot Wl (Addr.add (rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) ∧
              ((decide (rdx.toNat < 7) || decide (rdx = 7#64)) = true →
                  Q 248
                    { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64,
                      rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12,
                      r13 := r13, r14 := r14, r15 := r15 }
                    (rfz (subF (rfz (subF (rfz f) (rsp - 8 - 8 - 8 - 8 - 8 - 8) 8#64)) rdx 7#64))
                    (Vst
                      (Vst
                        (Vst
                          (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8))
                            (rsp - 8 - 8 - 8) (toBytesLE r13 8))
                          (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8))
                        (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8))
                      (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))) ∧
                ((decide (rdx.toNat < 7) || decide (rdx = 7#64)) = false →
                  (∀ (i : Nat), i < 4 → Foot F.data (Addr.add rsi i)) ∧
                    (decide (BitVec.setWidth 32 rdi = 3#32) = true →
                        Q 65
                          { rax := BitVec.setWidth 64 537202711#32, rcx := rcx,
                            rdx :=
                              BitVec.setWidth 64
                                (ofBytesLE 32
                                  (List.map
                                    (Vst
                                      (Vst
                                        (Vst
                                          (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8))
                                            (rsp - 8 - 8 - 8) (toBytesLE r13 8))
                                          (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8))
                                        (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8))
                                      (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))
                                    (byteAddrs rsi 4))),
                            rbx := rsi, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64,
                            rbp := BitVec.setWidth 64 (BitVec.setWidth 32 rdi), rsi := rsi, rdi := rdi, r8 := r8,
                            r9 := r9, r10 := r10, r11 := r11, r12 := rdx, r13 := r13, r14 := r14, r15 := r15 }
                          (rfz
                            (subF (rfz (subF (rfz (subF (rfz f) (rsp - 8 - 8 - 8 - 8 - 8 - 8) 8#64)) rdx 7#64))
                              (BitVec.setWidth 32 rdi) 3#32))
                          (Vst
                            (Vst
                              (Vst
                                (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8))
                                  (rsp - 8 - 8 - 8) (toBytesLE r13 8))
                                (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8))
                              (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8))
                            (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))) ∧
                      (decide (BitVec.setWidth 32 rdi = 3#32) = false →
                        ∀ (af af_1 : Bool),
                          Q 65
                            {
                              rax :=
                                BitVec.setWidth 64
                                  (if (BitVec.setWidth 32 rdi &&& BitVec.setWidth 32 rdi == 0) = true then 537462560#32
                                  else BitVec.setWidth 32 rdi ^^^ 537071893#32),
                              rcx := BitVec.setWidth 64 537462560#32,
                              rdx :=
                                BitVec.setWidth 64
                                  (ofBytesLE 32
                                    (List.map
                                      (Vst
                                        (Vst
                                          (Vst
                                            (Vst
                                              (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8))
                                              (rsp - 8 - 8 - 8) (toBytesLE r13 8))
                                            (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8))
                                          (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8))
                                        (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))
                                      (byteAddrs rsi 4))),
                              rbx := rsi, rsp := rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64,
                              rbp := BitVec.setWidth 64 (BitVec.setWidth 32 rdi), rsi := rsi, rdi := rdi, r8 := r8,
                              r9 := r9, r10 := r10, r11 := r11, r12 := rdx, r13 := r13, r14 := r14, r15 := r15 }
                            (rfz
                              ((rfz
                                    ((rfz
                                          (subF
                                            (rfz
                                              (subF (rfz (subF (rfz f) (rsp - 8 - 8 - 8 - 8 - 8 - 8) 8#64)) rdx 7#64))
                                            (BitVec.setWidth 32 rdi) 3#32)).arith
                                      (BitVec.setWidth 32 rdi ^^^ 537071893#32) false false af)).arith
                                (BitVec.setWidth 32 rdi &&& BitVec.setWidth 32 rdi) false false af_1))
                            (Vst
                              (Vst
                                (Vst
                                  (Vst (Vst (Vst V (rsp - 8) (toBytesLE r15 8)) (rsp - 8 - 8) (toBytesLE r14 8))
                                    (rsp - 8 - 8 - 8) (toBytesLE r13 8))
                                  (rsp - 8 - 8 - 8 - 8) (toBytesLE r12 8))
                                (rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE rbp 8))
                              (rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE rbx 8))))
=== cut 65
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ((!decide (BitVec.setWidth 32 rdx = BitVec.setWidth 32 rax)) = true →
      Q 248
        { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
          r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz f) (BitVec.setWidth 32 rdx) (BitVec.setWidth 32 rax))) V) ∧
    ((!decide (BitVec.setWidth 32 rdx = BitVec.setWidth 32 rax)) = false →
      (∀ (i : Nat), i < 4 → Foot F.data ((rbx + 4#64).add i)) ∧
        (∀ (i : Nat), i < 8 → Foot F.data ((7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 rbp) * 8#64).add i)) ∧
          (decide
                  ((BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4)))).toNat <
                    (ofBytesLE 64
                        (List.map V
                          (byteAddrs (7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 rbp) * 8#64) 8))).toNat) =
                true →
              Q 248
                { rax := 7270432#64, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
                  r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12,
                  r13 := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))),
                  r14 := BitVec.signExtend 64 (BitVec.setWidth 32 rbp), r15 := r15 }
                (rfz
                  (subF (rfz (subF (rfz f) (BitVec.setWidth 32 rdx) (BitVec.setWidth 32 rax)))
                    (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))))
                    (ofBytesLE 64
                      (List.map V (byteAddrs (7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 rbp) * 8#64) 8)))))
                V) ∧
            (decide
                  ((BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4)))).toNat <
                    (ofBytesLE 64
                        (List.map V
                          (byteAddrs (7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 rbp) * 8#64) 8))).toNat) =
                false →
              ((!decide
                        (BitVec.toNat
                            (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))) * 4#64 + 8#64) <
                          r12.toNat)) =
                    true →
                  Q 248
                    { rax := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))) * 4#64 + 8#64,
                      rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
                      r9 := r9, r10 := r10, r11 := r11, r12 := r12,
                      r13 := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))),
                      r14 := BitVec.signExtend 64 (BitVec.setWidth 32 rbp), r15 := r15 }
                    (rfz
                      (subF
                        (rfz
                          (subF (rfz (subF (rfz f) (BitVec.setWidth 32 rdx) (BitVec.setWidth 32 rax)))
                            (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))))
                            (ofBytesLE 64
                              (List.map V
                                (byteAddrs (7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 rbp) * 8#64) 8)))))
                        (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))) * 4#64 + 8#64) r12))
                    V) ∧
                ((!decide
                        (BitVec.toNat
                            (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))) * 4#64 + 8#64) <
                          r12.toNat)) =
                    false →
                  Q 122
                    { rax := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))) * 4#64 + 8#64,
                      rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi,
                      rdi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))) * 8#64 + 64#64,
                      r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12,
                      r13 := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))),
                      r14 := BitVec.signExtend 64 (BitVec.setWidth 32 rbp), r15 := r15 }
                    (rfz
                      (subF
                        (rfz
                          (subF (rfz (subF (rfz f) (BitVec.setWidth 32 rdx) (BitVec.setWidth 32 rax)))
                            (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))))
                            (ofBytesLE 64
                              (List.map V
                                (byteAddrs (7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 rbp) * 8#64) 8)))))
                        (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + 4#64) 4))) * 4#64 + 8#64) r12))
                    V)))
=== cut 127
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ∀ (af : Bool),
    ((rax &&& rax == 0) = true →
        Q 264
          { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
            r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
          (rfz ((rfz f).arith (rax &&& rax) false false af)) V) ∧
      ((rax &&& rax == 0) = false →
        (∀ (i : Nat), i < 8 → Foot Wl ((rax + 8#64).add i)) ∧
          (∀ (i : Nat), i < 8 → Foot Wl ((rax + 16#64).add i)) ∧
            (∀ (i : Nat), i < 8 → Foot Wl ((rax + 32#64).add i)) ∧
              (∀ (i : Nat), i < 8 → Foot Wl ((rax + 40#64).add i)) ∧
                (∀ (i : Nat), i < 8 → Foot Wl ((rax + 48#64).add i)) ∧
                  (∀ (i : Nat), i < 4 → Foot Wl ((rax + 56#64).add i)) ∧
                    ∀ (af_1 : Bool),
                      ((r13 &&& r13 == 0) = true →
                          Q 264
                            { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi,
                              rdi := rdi, r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13,
                              r14 := r14, r15 := r15 }
                            (rfz
                              ((rfz ((rfz f).arith (rax &&& rax) false false af)).arith (r13 &&& r13) false false af_1))
                            (Vst
                              (Vst
                                (Vst
                                  (Vst (Vst (Vst V (rax + 8#64) (toBytesLE rbx 8)) (rax + 16#64) (toBytesLE r12 8))
                                    (rax + 32#64) (toBytesLE (0#64) 8))
                                  (rax + 40#64) (toBytesLE (0#64) 8))
                                (rax + 48#64) (toBytesLE (0#64) 8))
                              (rax + 56#64) (toBytesLE (BitVec.setWidth 32 r13) 4))) ∧
                        ((r13 &&& r13 == 0) = false →
                          ∀ (af_2 : Bool),
                            Q 196
                              { rax := rax,
                                rcx := BitVec.setWidth 64 (BitVec.setWidth 32 rcx ^^^ BitVec.setWidth 32 rcx),
                                rdx := 7268832#64, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
                                r9 := BitVec.setWidth 64 (BitVec.setWidth 32 rbp), r10 := 7865536#64, r11 := r11,
                                r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
                              (rfz
                                ((rfz
                                      ((rfz ((rfz f).arith (rax &&& rax) false false af)).arith (r13 &&& r13) false
                                        false af_1)).arith
                                  (BitVec.setWidth 32 rcx ^^^ BitVec.setWidth 32 rcx) false false af_2))
                              (Vst
                                (Vst
                                  (Vst
                                    (Vst (Vst (Vst V (rax + 8#64) (toBytesLE rbx 8)) (rax + 16#64) (toBytesLE r12 8))
                                      (rax + 32#64) (toBytesLE (0#64) 8))
                                    (rax + 40#64) (toBytesLE (0#64) 8))
                                  (rax + 48#64) (toBytesLE (0#64) 8))
                                (rax + 56#64) (toBytesLE (BitVec.setWidth 32 r13) 4))))
=== cut 196
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ (∀ (i : Nat), i < 4 → Foot F.data ((rbx + rcx * 4#64 + 8#64).add i)) ∧
    (decide
            (r12.toNat <
              (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4)))).toNat) =
          true →
        Q 240
          { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
            rsi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))),
            rdi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))), r8 := r8,
            r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
          (rfz
            (subF (rfz f) r12 (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))))))
          V) ∧
      (decide
            (r12.toNat <
              (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4)))).toNat) =
          false →
        ((!(decide ((BitVec.setWidth 32 rbp).toNat < 12) || decide (BitVec.setWidth 32 rbp = 12#32))) = true →
            Q 435
              { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
                rsi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))),
                rdi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))), r8 := r8,
                r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
              (rfz
                (subF
                  (rfz
                    (subF (rfz f) r12
                      (BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))))))
                  (BitVec.setWidth 32 rbp) 12#32))
              V) ∧
          ((!(decide ((BitVec.setWidth 32 rbp).toNat < 12) || decide (BitVec.setWidth 32 rbp = 12#32))) = false →
            (∀ (i : Nat), i < 4 → Foot F.data ((rdx + r9 * 4#64).add i)) ∧
              ∃ tgt,
                tgt < Ild.ild.length ∧
                  BitVec.signExtend 64 (ofBytesLE 32 (List.map V (byteAddrs (rdx + r9 * 4#64) 4))) + rdx =
                      Ild.ild_at.add tgt ∧
                    Q tgt
                      { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
                        rsi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))),
                        rdi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))),
                        r8 := BitVec.signExtend 64 (ofBytesLE 32 (List.map V (byteAddrs (rdx + r9 * 4#64) 4))) + rdx,
                        r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
                      (rfz
                        (addF
                          (rfz
                            (subF
                              (rfz
                                (subF (rfz f) r12
                                  (BitVec.setWidth 64
                                    (ofBytesLE 32 (List.map V (byteAddrs (rbx + rcx * 4#64 + 8#64) 4))))))
                              (BitVec.setWidth 32 rbp) 12#32))
                          (BitVec.signExtend 64 (ofBytesLE 32 (List.map V (byteAddrs (rdx + r9 * 4#64) 4)))) rdx))
                      V))
=== cut 228
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ((decide (rcx.toNat < 1) || decide (rcx = 1#64)) = true →
      Q 288
        { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
          r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz f) rcx 1#64)) V) ∧
    ((decide (rcx.toNat < 1) || decide (rcx = 1#64)) = false →
      Q 240
        { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
          r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz f) rcx 1#64)) V)
=== cut 240
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ Q 243
    { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rax, r8 := r8,
      r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
    (rfz f) V
=== cut 248
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ (∀ (i : Nat), i < 4 → Foot Wl ((fb + 18446744073709551544#64).add i)) ∧
    ∀ (af : Bool),
      Q 264
        {
          rax :=
            BitVec.setWidth 64
              (BitVec.setWidth 32 18446744073709551544#64 ^^^ BitVec.setWidth 32 18446744073709551544#64),
          rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8, r9 := r9,
          r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        ((rfz f).arith (BitVec.setWidth 32 18446744073709551544#64 ^^^ BitVec.setWidth 32 18446744073709551544#64) false
          false af)
        (Vst V (fb + 18446744073709551544#64) (toBytesLE (22#32) 4))
=== cut 264
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ (∀ (i : Nat), i < 8 → Foot F.data (Addr.add (rsp + 8#64) i)) ∧
    (∀ (i : Nat), i < 8 → Foot F.data (Addr.add (rsp + 8#64 + 8) i)) ∧
      (∀ (i : Nat), i < 8 → Foot F.data (Addr.add (rsp + 8#64 + 8 + 8) i)) ∧
        (∀ (i : Nat), i < 8 → Foot F.data (Addr.add (rsp + 8#64 + 8 + 8 + 8) i)) ∧
          (∀ (i : Nat), i < 8 → Foot F.data (Addr.add (rsp + 8#64 + 8 + 8 + 8 + 8) i)) ∧
            (∀ (i : Nat), i < 8 → Foot F.data (Addr.add (rsp + 8#64 + 8 + 8 + 8 + 8 + 8) i)) ∧
              Q 278
                { rax := rax, rcx := rcx, rdx := rdx, rbx := ofBytesLE 64 (List.map V (byteAddrs (rsp + 8#64) 8)),
                  rsp := rsp + 8#64 + 8 + 8 + 8 + 8 + 8 + 8,
                  rbp := ofBytesLE 64 (List.map V (byteAddrs (rsp + 8#64 + 8) 8)), rsi := rsi, rdi := rdi, r8 := r8,
                  r9 := r9, r10 := r10, r11 := r11, r12 := ofBytesLE 64 (List.map V (byteAddrs (rsp + 8#64 + 8 + 8) 8)),
                  r13 := ofBytesLE 64 (List.map V (byteAddrs (rsp + 8#64 + 8 + 8 + 8) 8)),
                  r14 := ofBytesLE 64 (List.map V (byteAddrs (rsp + 8#64 + 8 + 8 + 8 + 8) 8)),
                  r15 := ofBytesLE 64 (List.map V (byteAddrs (rsp + 8#64 + 8 + 8 + 8 + 8 + 8) 8)) }
                (rfz (addF (rfz f) rsp 8#64)) V
=== cut 279
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ((!(decide (rcx.toNat < 4) || decide (rcx = 4#64))) = true →
      Q 240
        { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
          r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz f) rcx 4#64)) V) ∧
    ((!(decide (rcx.toNat < 4) || decide (rcx = 4#64))) = false →
      Q 288
        { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
          r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz f) rcx 4#64)) V)
=== cut 288
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ (∀ (i : Nat), i < 8 → Foot F.data ((r10 + r14 * 8#64).add i)) ∧
    (∀ (i : Nat),
        i < 4 → Foot F.data ((ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64).add i)) ∧
      (decide
              (ofBytesLE 32
                  (List.map V (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)) =
                5#32) =
            true →
          Q 336
            { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
              r8 := ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)), r9 := r9, r10 := r10, r11 := r11,
              r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
            (rfz
              (subF (rfz f)
                (ofBytesLE 32
                  (List.map V (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)))
                5#32))
            V) ∧
        (decide
              (ofBytesLE 32
                  (List.map V (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)) =
                5#32) =
            false →
          Q 299
            { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
              r8 := ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)), r9 := r9, r10 := r10, r11 := r11,
              r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
            (rfz
              (subF (rfz f)
                (ofBytesLE 32
                  (List.map V (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)))
                5#32))
            V)
=== cut 299
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ (∀ (i : Nat), i < 8 → Foot Wl ((rax + rcx * 8#64 + 64#64).add i)) ∧
    Q 307
      { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi + rbx, r8 := r8,
        r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
      (rfz (addF (rfz f) rdi rbx)) (Vst V (rax + rcx * 8#64 + 64#64) (toBytesLE (rdi + rbx) 8))
=== cut 307
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ((!decide (r13 = rcx + 1#64)) = true →
      Q 196
        { rax := rax, rcx := rcx + 1#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
          r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz (addF (rfz f) rcx 1#64)) r13 (rcx + 1#64))) V) ∧
    ((!decide (r13 = rcx + 1#64)) = false →
      Q 264
        { rax := rax, rcx := rcx + 1#64, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
          r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz (addF (rfz f) rcx 1#64)) r13 (rcx + 1#64))) V)
=== cut 318
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ((!(decide (rcx.toNat < 12) || decide (rcx = 12#64))) = true →
      Q 240
        { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
          r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
        (rfz (subF (rfz f) rcx 12#64)) V) ∧
    ((!(decide (rcx.toNat < 12) || decide (rcx = 12#64))) = false →
      (∀ (i : Nat), i < 8 → Foot F.data ((r10 + r14 * 8#64).add i)) ∧
        (∀ (i : Nat),
            i < 4 → Foot F.data ((ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64).add i)) ∧
          ((!decide
                    (ofBytesLE 32
                        (List.map V
                          (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)) =
                      5#32)) =
                true →
              Q 299
                { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
                  r8 := ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)), r9 := r9, r10 := r10, r11 := r11,
                  r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
                (rfz
                  (subF (rfz (subF (rfz f) rcx 12#64))
                    (ofBytesLE 32
                      (List.map V
                        (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)))
                    5#32))
                V) ∧
            ((!decide
                    (ofBytesLE 32
                        (List.map V
                          (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)) =
                      5#32)) =
                false →
              Q 336
                { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
                  r8 := ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)), r9 := r9, r10 := r10, r11 := r11,
                  r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
                (rfz
                  (subF (rfz (subF (rfz f) rcx 12#64))
                    (ofBytesLE 32
                      (List.map V
                        (byteAddrs (ofBytesLE 64 (List.map V (byteAddrs (r10 + r14 * 8#64) 8)) + rcx * 4#64) 4)))
                    5#32))
                V))
=== cut 336
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ∀ (af : Bool),
    ((!BitVec.setWidth 32 rsi &&& 3#32 == 0) = true →
        Q 240
          { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
            rsi := BitVec.setWidth 64 (BitVec.setWidth 32 rsi &&& 3#32), rdi := rdi, r8 := r8, r9 := r9, r10 := r10,
            r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
          (rfz ((rfz f).arith (BitVec.setWidth 32 rsi &&& 3#32) false false af)) V) ∧
      ((!BitVec.setWidth 32 rsi &&& 3#32 == 0) = false →
        (∀ (i : Nat), i < 4 → Foot F.data ((rbx + rdi).add i)) ∧
          (∀ (i : Nat), i < 4 → Foot Wl ((rax + rcx * 8#64 + 64#64).add i)) ∧
            Q 307
              { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp,
                rsi := BitVec.setWidth 64 (ofBytesLE 32 (List.map V (byteAddrs (rbx + rdi) 4))), rdi := rdi, r8 := r8,
                r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
              (rfz ((rfz f).arith (BitVec.setWidth 32 rsi &&& 3#32) false false af))
              (Vst V (rax + rcx * 8#64 + 64#64) (toBytesLE (ofBytesLE 32 (List.map V (byteAddrs (rbx + rdi) 4))) 4)))
=== cut 435
Wl : List Rgn
fb : Addr
f : Rflags
V : Addr → Byte
Q : Post
rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64
⊢ ∀ (af : Bool),
    ((!BitVec.setWidth 32 rbp &&& BitVec.setWidth 32 rbp == 0) = true →
        Q 454
          { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi, r8 := r8,
            r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
          (rfz ((rfz f).arith (BitVec.setWidth 32 rbp &&& BitVec.setWidth 32 rbp) false false af)) V) ∧
      ((!BitVec.setWidth 32 rbp &&& BitVec.setWidth 32 rbp == 0) = false →
        ((!(decide (rcx.toNat < 85) || decide (rcx = 85#64))) = true →
            Q 299
              { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
                r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
              (rfz
                (subF (rfz ((rfz f).arith (BitVec.setWidth 32 rbp &&& BitVec.setWidth 32 rbp) false false af)) rcx
                  85#64))
              V) ∧
          ((!(decide (rcx.toNat < 85) || decide (rcx = 85#64))) = false →
            Q 288
              { rax := rax, rcx := rcx, rdx := rdx, rbx := rbx, rsp := rsp, rbp := rbp, rsi := rsi, rdi := rdi,
                r8 := r8, r9 := r9, r10 := r10, r11 := r11, r12 := r12, r13 := r13, r14 := r14, r15 := r15 }
              (rfz
                (subF (rfz ((rfz f).arith (BitVec.setWidth 32 rbp &&& BitVec.setWidth 32 rbp) false false af)) rcx
                  85#64))
              V))
-/
