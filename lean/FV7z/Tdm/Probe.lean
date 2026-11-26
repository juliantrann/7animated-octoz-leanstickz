import FV7z.Tdm.Cuts
/-! Probe: the goals after `wpx` at each cut point (triage only). -/
open ZellicX86 Decode FV7z FV7z.Leaf
namespace FV7z.Tdm.Probe
open FV7z.Tdm
set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
theorem p_0 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, W_74, W_86, o0, o1, o2, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_103 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_103 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_103, W_360, W_121, W_386, W_135, W_394, W_1056, o3, o20, o4, o21, o5, o22, o54, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_180 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_180 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_180, o6, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_210 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_210 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_210, W_768, W_220, W_1072, o7, o42, o8, o55, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_248 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_248 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_248, W_262, W_271, o10, o11, o12, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_288 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_288 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_288, W_232, W_304, o13, o9, o14, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_314 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_314 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_314, o15, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_320 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_320 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_320, W_327, W_336, o16, o11, o17, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_340 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_340 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_340, o18, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_343 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_343 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_343, o19, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_411 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_411 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_411, W_912, W_428, W_931, W_943, o23, o49, o24, o21, o22, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_443 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_443 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_443, W_455, W_464, o25, o11, o26, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_481 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_481 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_481, W_720, W_498, W_742, W_1088, o27, o40, o28, o11, o26, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_510 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_510 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_510, o8, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_532 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_532 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_532, W_546, W_555, o30, o11, o12, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_572 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_572 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_572, W_520, W_588, o31, o29, o32, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_594 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_594 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_594, W_603, o33, o34, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_648 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_648 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_648, W_1360, W_1372, W_1501, W_1381, o36, o63, o64, o74, o65, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_657 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_657 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_657, W_674, W_679, o37, o11, o12, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_696 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_696 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_696, W_640, W_712, o38, o35, o39, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_751 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_751 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_751, o41, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_794 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_794 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_794, o43, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_821 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_821 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_821, o45, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_833 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_833 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_833, W_858, W_863, o46, o11, o12, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_880 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_880 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_880, W_816, W_896, o47, o44, o48, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_960 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_960 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_960, W_1152, W_977, W_1171, W_994, W_1183, W_1006, o23, o57, o50, o21, o22, o51, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1024 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1024 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1024, W_1344, W_1044, o52, o62, o53, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1105 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1105 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1105, W_1312, W_1122, o27, o61, o56, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1200 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1200 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1200, W_1213, W_1232, W_1244, o23, o58, o21, o22, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1261 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1261 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1261, W_1274, o23, o59, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1288 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1288 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1288, o60, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1400 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1400 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1400, o66, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1420 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1420 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1420, W_1429, o68, o69, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1432 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1432 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1432, W_1446, W_1455, o70, o11, o71, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1472 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1472 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1472, W_1416, W_1491, o72, o67, o73, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1504 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1504 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1504, W_1511, W_1520, o16, o11, o12, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

set_option maxHeartbeats 4000000 in
theorem p_1537 {F : Footprint} {Wl : List Rgn} {Q : Post} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_1537 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1537, W_1560, o75, o76, Op.not32, Op.cmpmi]
  repeat' (first | apply And.intro | intro _)
  trace_state
  all_goals sorry

end FV7z.Tdm.Probe
