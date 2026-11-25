/-
GENERATED FILE -- do not edit.  Produced by scripts/gen_cases.py from the run logs
  data/frame/d_48_24.jsonl.xz     ( 47580 records, sha256 of the uncompressed text b2da856bcae39f885b5744efba907cdaa20251f6116a605937bbb4618a1c73b0)
of the frame-method run for n = 48, k = 24: 47580 cases, 14365 frames;
47580 refuted by a plain record (UNSAT, drat-trim VERIFIED), 0 by verified cube records of run_hard.py.
Kernel computations: the case list `L(48, 24)` is the decoded table `caseCodes48T`, checked piece
by piece (one theorem per pair of horizontal margins (ml, mr), so that each kernel computation is
small and the pieces are checked in parallel).  No `native_decide`.
-/

module

public import QueenDom.Main
public import Queens48.Cases48Data

@[expose] public section

namespace QueenDom

set_option maxRecDepth 100000 in
/-- The 325 pairs `(ml, mr)` with `ml + mr <= 24`. -/
theorem marginPairs_24 : marginPairs 24 = [
    (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
    (0, 12), (0, 13), (0, 14), (0, 15), (0, 16), (0, 17), (0, 18), (0, 19), (0, 20), (0, 21), (0, 22), (0, 23),
    (0, 24), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (1, 10),
    (1, 11), (1, 12), (1, 13), (1, 14), (1, 15), (1, 16), (1, 17), (1, 18), (1, 19), (1, 20), (1, 21), (1, 22),
    (1, 23), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (2, 10),
    (2, 11), (2, 12), (2, 13), (2, 14), (2, 15), (2, 16), (2, 17), (2, 18), (2, 19), (2, 20), (2, 21), (2, 22),
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (3, 10), (3, 11),
    (3, 12), (3, 13), (3, 14), (3, 15), (3, 16), (3, 17), (3, 18), (3, 19), (3, 20), (3, 21), (4, 0), (4, 1),
    (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (4, 9), (4, 10), (4, 11), (4, 12), (4, 13),
    (4, 14), (4, 15), (4, 16), (4, 17), (4, 18), (4, 19), (4, 20), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4),
    (5, 5), (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11), (5, 12), (5, 13), (5, 14), (5, 15), (5, 16),
    (5, 17), (5, 18), (5, 19), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (6, 8),
    (6, 9), (6, 10), (6, 11), (6, 12), (6, 13), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18), (7, 0), (7, 1),
    (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12), (7, 13),
    (7, 14), (7, 15), (7, 16), (7, 17), (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6), (8, 7),
    (8, 8), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13), (8, 14), (8, 15), (8, 16), (9, 0), (9, 1), (9, 2),
    (9, 3), (9, 4), (9, 5), (9, 6), (9, 7), (9, 8), (9, 9), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14),
    (9, 15), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5), (10, 6), (10, 7), (10, 8), (10, 9), (10, 10),
    (10, 11), (10, 12), (10, 13), (10, 14), (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (11, 6), (11, 7),
    (11, 8), (11, 9), (11, 10), (11, 11), (11, 12), (11, 13), (12, 0), (12, 1), (12, 2), (12, 3), (12, 4), (12, 5),
    (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4),
    (13, 5), (13, 6), (13, 7), (13, 8), (13, 9), (13, 10), (13, 11), (14, 0), (14, 1), (14, 2), (14, 3), (14, 4),
    (14, 5), (14, 6), (14, 7), (14, 8), (14, 9), (14, 10), (15, 0), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5),
    (15, 6), (15, 7), (15, 8), (15, 9), (16, 0), (16, 1), (16, 2), (16, 3), (16, 4), (16, 5), (16, 6), (16, 7),
    (16, 8), (17, 0), (17, 1), (17, 2), (17, 3), (17, 4), (17, 5), (17, 6), (17, 7), (18, 0), (18, 1), (18, 2),
    (18, 3), (18, 4), (18, 5), (18, 6), (19, 0), (19, 1), (19, 2), (19, 3), (19, 4), (19, 5), (20, 0), (20, 1),
    (20, 2), (20, 3), (20, 4), (21, 0), (21, 1), (21, 2), (21, 3), (22, 0), (22, 1), (22, 2), (23, 0), (23, 1),
    (24, 0)
  ] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_0 : casesPQ 48 24 0 0 = (tableCodes caseCodes48T 0 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_1 : casesPQ 48 24 0 1 = (tableCodes caseCodes48T 0 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_2 : casesPQ 48 24 0 2 = (tableCodes caseCodes48T 0 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_3 : casesPQ 48 24 0 3 = (tableCodes caseCodes48T 0 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_4 : casesPQ 48 24 0 4 = (tableCodes caseCodes48T 0 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_5 : casesPQ 48 24 0 5 = (tableCodes caseCodes48T 0 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_6 : casesPQ 48 24 0 6 = (tableCodes caseCodes48T 0 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_7 : casesPQ 48 24 0 7 = (tableCodes caseCodes48T 0 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_8 : casesPQ 48 24 0 8 = (tableCodes caseCodes48T 0 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_9 : casesPQ 48 24 0 9 = (tableCodes caseCodes48T 0 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_10 : casesPQ 48 24 0 10 = (tableCodes caseCodes48T 0 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_11 : casesPQ 48 24 0 11 = (tableCodes caseCodes48T 0 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_12 : casesPQ 48 24 0 12 = (tableCodes caseCodes48T 0 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_13 : casesPQ 48 24 0 13 = (tableCodes caseCodes48T 0 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_14 : casesPQ 48 24 0 14 = (tableCodes caseCodes48T 0 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_15 : casesPQ 48 24 0 15 = (tableCodes caseCodes48T 0 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_16 : casesPQ 48 24 0 16 = (tableCodes caseCodes48T 0 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_17 : casesPQ 48 24 0 17 = (tableCodes caseCodes48T 0 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_18 : casesPQ 48 24 0 18 = (tableCodes caseCodes48T 0 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_19 : casesPQ 48 24 0 19 = (tableCodes caseCodes48T 0 19).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_20 : casesPQ 48 24 0 20 = (tableCodes caseCodes48T 0 20).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_21 : casesPQ 48 24 0 21 = (tableCodes caseCodes48T 0 21).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_22 : casesPQ 48 24 0 22 = (tableCodes caseCodes48T 0 22).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_23 : casesPQ 48 24 0 23 = (tableCodes caseCodes48T 0 23).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_0_24 : casesPQ 48 24 0 24 = (tableCodes caseCodes48T 0 24).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_0 : casesPQ 48 24 1 0 = (tableCodes caseCodes48T 1 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_1 : casesPQ 48 24 1 1 = (tableCodes caseCodes48T 1 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_2 : casesPQ 48 24 1 2 = (tableCodes caseCodes48T 1 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_3 : casesPQ 48 24 1 3 = (tableCodes caseCodes48T 1 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_4 : casesPQ 48 24 1 4 = (tableCodes caseCodes48T 1 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_5 : casesPQ 48 24 1 5 = (tableCodes caseCodes48T 1 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_6 : casesPQ 48 24 1 6 = (tableCodes caseCodes48T 1 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_7 : casesPQ 48 24 1 7 = (tableCodes caseCodes48T 1 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_8 : casesPQ 48 24 1 8 = (tableCodes caseCodes48T 1 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_9 : casesPQ 48 24 1 9 = (tableCodes caseCodes48T 1 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_10 : casesPQ 48 24 1 10 = (tableCodes caseCodes48T 1 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_11 : casesPQ 48 24 1 11 = (tableCodes caseCodes48T 1 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_12 : casesPQ 48 24 1 12 = (tableCodes caseCodes48T 1 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_13 : casesPQ 48 24 1 13 = (tableCodes caseCodes48T 1 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_14 : casesPQ 48 24 1 14 = (tableCodes caseCodes48T 1 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_15 : casesPQ 48 24 1 15 = (tableCodes caseCodes48T 1 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_16 : casesPQ 48 24 1 16 = (tableCodes caseCodes48T 1 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_17 : casesPQ 48 24 1 17 = (tableCodes caseCodes48T 1 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_18 : casesPQ 48 24 1 18 = (tableCodes caseCodes48T 1 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_19 : casesPQ 48 24 1 19 = (tableCodes caseCodes48T 1 19).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_20 : casesPQ 48 24 1 20 = (tableCodes caseCodes48T 1 20).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_21 : casesPQ 48 24 1 21 = (tableCodes caseCodes48T 1 21).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_22 : casesPQ 48 24 1 22 = (tableCodes caseCodes48T 1 22).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_1_23 : casesPQ 48 24 1 23 = (tableCodes caseCodes48T 1 23).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_0 : casesPQ 48 24 2 0 = (tableCodes caseCodes48T 2 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_1 : casesPQ 48 24 2 1 = (tableCodes caseCodes48T 2 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_2 : casesPQ 48 24 2 2 = (tableCodes caseCodes48T 2 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_3 : casesPQ 48 24 2 3 = (tableCodes caseCodes48T 2 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_4 : casesPQ 48 24 2 4 = (tableCodes caseCodes48T 2 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_5 : casesPQ 48 24 2 5 = (tableCodes caseCodes48T 2 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_6 : casesPQ 48 24 2 6 = (tableCodes caseCodes48T 2 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_7 : casesPQ 48 24 2 7 = (tableCodes caseCodes48T 2 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_8 : casesPQ 48 24 2 8 = (tableCodes caseCodes48T 2 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_9 : casesPQ 48 24 2 9 = (tableCodes caseCodes48T 2 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_10 : casesPQ 48 24 2 10 = (tableCodes caseCodes48T 2 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_11 : casesPQ 48 24 2 11 = (tableCodes caseCodes48T 2 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_12 : casesPQ 48 24 2 12 = (tableCodes caseCodes48T 2 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_13 : casesPQ 48 24 2 13 = (tableCodes caseCodes48T 2 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_14 : casesPQ 48 24 2 14 = (tableCodes caseCodes48T 2 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_15 : casesPQ 48 24 2 15 = (tableCodes caseCodes48T 2 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_16 : casesPQ 48 24 2 16 = (tableCodes caseCodes48T 2 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_17 : casesPQ 48 24 2 17 = (tableCodes caseCodes48T 2 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_18 : casesPQ 48 24 2 18 = (tableCodes caseCodes48T 2 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_19 : casesPQ 48 24 2 19 = (tableCodes caseCodes48T 2 19).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_20 : casesPQ 48 24 2 20 = (tableCodes caseCodes48T 2 20).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_21 : casesPQ 48 24 2 21 = (tableCodes caseCodes48T 2 21).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_2_22 : casesPQ 48 24 2 22 = (tableCodes caseCodes48T 2 22).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_0 : casesPQ 48 24 3 0 = (tableCodes caseCodes48T 3 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_1 : casesPQ 48 24 3 1 = (tableCodes caseCodes48T 3 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_2 : casesPQ 48 24 3 2 = (tableCodes caseCodes48T 3 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_3 : casesPQ 48 24 3 3 = (tableCodes caseCodes48T 3 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_4 : casesPQ 48 24 3 4 = (tableCodes caseCodes48T 3 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_5 : casesPQ 48 24 3 5 = (tableCodes caseCodes48T 3 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_6 : casesPQ 48 24 3 6 = (tableCodes caseCodes48T 3 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_7 : casesPQ 48 24 3 7 = (tableCodes caseCodes48T 3 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_8 : casesPQ 48 24 3 8 = (tableCodes caseCodes48T 3 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_9 : casesPQ 48 24 3 9 = (tableCodes caseCodes48T 3 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_10 : casesPQ 48 24 3 10 = (tableCodes caseCodes48T 3 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_11 : casesPQ 48 24 3 11 = (tableCodes caseCodes48T 3 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_12 : casesPQ 48 24 3 12 = (tableCodes caseCodes48T 3 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_13 : casesPQ 48 24 3 13 = (tableCodes caseCodes48T 3 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_14 : casesPQ 48 24 3 14 = (tableCodes caseCodes48T 3 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_15 : casesPQ 48 24 3 15 = (tableCodes caseCodes48T 3 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_16 : casesPQ 48 24 3 16 = (tableCodes caseCodes48T 3 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_17 : casesPQ 48 24 3 17 = (tableCodes caseCodes48T 3 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_18 : casesPQ 48 24 3 18 = (tableCodes caseCodes48T 3 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_19 : casesPQ 48 24 3 19 = (tableCodes caseCodes48T 3 19).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_20 : casesPQ 48 24 3 20 = (tableCodes caseCodes48T 3 20).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_3_21 : casesPQ 48 24 3 21 = (tableCodes caseCodes48T 3 21).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_0 : casesPQ 48 24 4 0 = (tableCodes caseCodes48T 4 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_1 : casesPQ 48 24 4 1 = (tableCodes caseCodes48T 4 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_2 : casesPQ 48 24 4 2 = (tableCodes caseCodes48T 4 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_3 : casesPQ 48 24 4 3 = (tableCodes caseCodes48T 4 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_4 : casesPQ 48 24 4 4 = (tableCodes caseCodes48T 4 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_5 : casesPQ 48 24 4 5 = (tableCodes caseCodes48T 4 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_6 : casesPQ 48 24 4 6 = (tableCodes caseCodes48T 4 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_7 : casesPQ 48 24 4 7 = (tableCodes caseCodes48T 4 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_8 : casesPQ 48 24 4 8 = (tableCodes caseCodes48T 4 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_9 : casesPQ 48 24 4 9 = (tableCodes caseCodes48T 4 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_10 : casesPQ 48 24 4 10 = (tableCodes caseCodes48T 4 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_11 : casesPQ 48 24 4 11 = (tableCodes caseCodes48T 4 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_12 : casesPQ 48 24 4 12 = (tableCodes caseCodes48T 4 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_13 : casesPQ 48 24 4 13 = (tableCodes caseCodes48T 4 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_14 : casesPQ 48 24 4 14 = (tableCodes caseCodes48T 4 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_15 : casesPQ 48 24 4 15 = (tableCodes caseCodes48T 4 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_16 : casesPQ 48 24 4 16 = (tableCodes caseCodes48T 4 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_17 : casesPQ 48 24 4 17 = (tableCodes caseCodes48T 4 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_18 : casesPQ 48 24 4 18 = (tableCodes caseCodes48T 4 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_19 : casesPQ 48 24 4 19 = (tableCodes caseCodes48T 4 19).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_4_20 : casesPQ 48 24 4 20 = (tableCodes caseCodes48T 4 20).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_0 : casesPQ 48 24 5 0 = (tableCodes caseCodes48T 5 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_1 : casesPQ 48 24 5 1 = (tableCodes caseCodes48T 5 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_2 : casesPQ 48 24 5 2 = (tableCodes caseCodes48T 5 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_3 : casesPQ 48 24 5 3 = (tableCodes caseCodes48T 5 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_4 : casesPQ 48 24 5 4 = (tableCodes caseCodes48T 5 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_5 : casesPQ 48 24 5 5 = (tableCodes caseCodes48T 5 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_6 : casesPQ 48 24 5 6 = (tableCodes caseCodes48T 5 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_7 : casesPQ 48 24 5 7 = (tableCodes caseCodes48T 5 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_8 : casesPQ 48 24 5 8 = (tableCodes caseCodes48T 5 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_9 : casesPQ 48 24 5 9 = (tableCodes caseCodes48T 5 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_10 : casesPQ 48 24 5 10 = (tableCodes caseCodes48T 5 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_11 : casesPQ 48 24 5 11 = (tableCodes caseCodes48T 5 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_12 : casesPQ 48 24 5 12 = (tableCodes caseCodes48T 5 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_13 : casesPQ 48 24 5 13 = (tableCodes caseCodes48T 5 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_14 : casesPQ 48 24 5 14 = (tableCodes caseCodes48T 5 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_15 : casesPQ 48 24 5 15 = (tableCodes caseCodes48T 5 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_16 : casesPQ 48 24 5 16 = (tableCodes caseCodes48T 5 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_17 : casesPQ 48 24 5 17 = (tableCodes caseCodes48T 5 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_18 : casesPQ 48 24 5 18 = (tableCodes caseCodes48T 5 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_5_19 : casesPQ 48 24 5 19 = (tableCodes caseCodes48T 5 19).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_0 : casesPQ 48 24 6 0 = (tableCodes caseCodes48T 6 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_1 : casesPQ 48 24 6 1 = (tableCodes caseCodes48T 6 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_2 : casesPQ 48 24 6 2 = (tableCodes caseCodes48T 6 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_3 : casesPQ 48 24 6 3 = (tableCodes caseCodes48T 6 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_4 : casesPQ 48 24 6 4 = (tableCodes caseCodes48T 6 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_5 : casesPQ 48 24 6 5 = (tableCodes caseCodes48T 6 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_6 : casesPQ 48 24 6 6 = (tableCodes caseCodes48T 6 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_7 : casesPQ 48 24 6 7 = (tableCodes caseCodes48T 6 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_8 : casesPQ 48 24 6 8 = (tableCodes caseCodes48T 6 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_9 : casesPQ 48 24 6 9 = (tableCodes caseCodes48T 6 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_10 : casesPQ 48 24 6 10 = (tableCodes caseCodes48T 6 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_11 : casesPQ 48 24 6 11 = (tableCodes caseCodes48T 6 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_12 : casesPQ 48 24 6 12 = (tableCodes caseCodes48T 6 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_13 : casesPQ 48 24 6 13 = (tableCodes caseCodes48T 6 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_14 : casesPQ 48 24 6 14 = (tableCodes caseCodes48T 6 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_15 : casesPQ 48 24 6 15 = (tableCodes caseCodes48T 6 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_16 : casesPQ 48 24 6 16 = (tableCodes caseCodes48T 6 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_17 : casesPQ 48 24 6 17 = (tableCodes caseCodes48T 6 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_6_18 : casesPQ 48 24 6 18 = (tableCodes caseCodes48T 6 18).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_0 : casesPQ 48 24 7 0 = (tableCodes caseCodes48T 7 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_1 : casesPQ 48 24 7 1 = (tableCodes caseCodes48T 7 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_2 : casesPQ 48 24 7 2 = (tableCodes caseCodes48T 7 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_3 : casesPQ 48 24 7 3 = (tableCodes caseCodes48T 7 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_4 : casesPQ 48 24 7 4 = (tableCodes caseCodes48T 7 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_5 : casesPQ 48 24 7 5 = (tableCodes caseCodes48T 7 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_6 : casesPQ 48 24 7 6 = (tableCodes caseCodes48T 7 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_7 : casesPQ 48 24 7 7 = (tableCodes caseCodes48T 7 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_8 : casesPQ 48 24 7 8 = (tableCodes caseCodes48T 7 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_9 : casesPQ 48 24 7 9 = (tableCodes caseCodes48T 7 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_10 : casesPQ 48 24 7 10 = (tableCodes caseCodes48T 7 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_11 : casesPQ 48 24 7 11 = (tableCodes caseCodes48T 7 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_12 : casesPQ 48 24 7 12 = (tableCodes caseCodes48T 7 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_13 : casesPQ 48 24 7 13 = (tableCodes caseCodes48T 7 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_14 : casesPQ 48 24 7 14 = (tableCodes caseCodes48T 7 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_15 : casesPQ 48 24 7 15 = (tableCodes caseCodes48T 7 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_16 : casesPQ 48 24 7 16 = (tableCodes caseCodes48T 7 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_7_17 : casesPQ 48 24 7 17 = (tableCodes caseCodes48T 7 17).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_0 : casesPQ 48 24 8 0 = (tableCodes caseCodes48T 8 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_1 : casesPQ 48 24 8 1 = (tableCodes caseCodes48T 8 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_2 : casesPQ 48 24 8 2 = (tableCodes caseCodes48T 8 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_3 : casesPQ 48 24 8 3 = (tableCodes caseCodes48T 8 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_4 : casesPQ 48 24 8 4 = (tableCodes caseCodes48T 8 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_5 : casesPQ 48 24 8 5 = (tableCodes caseCodes48T 8 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_6 : casesPQ 48 24 8 6 = (tableCodes caseCodes48T 8 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_7 : casesPQ 48 24 8 7 = (tableCodes caseCodes48T 8 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_8 : casesPQ 48 24 8 8 = (tableCodes caseCodes48T 8 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_9 : casesPQ 48 24 8 9 = (tableCodes caseCodes48T 8 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_10 : casesPQ 48 24 8 10 = (tableCodes caseCodes48T 8 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_11 : casesPQ 48 24 8 11 = (tableCodes caseCodes48T 8 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_12 : casesPQ 48 24 8 12 = (tableCodes caseCodes48T 8 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_13 : casesPQ 48 24 8 13 = (tableCodes caseCodes48T 8 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_14 : casesPQ 48 24 8 14 = (tableCodes caseCodes48T 8 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_15 : casesPQ 48 24 8 15 = (tableCodes caseCodes48T 8 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_8_16 : casesPQ 48 24 8 16 = (tableCodes caseCodes48T 8 16).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_0 : casesPQ 48 24 9 0 = (tableCodes caseCodes48T 9 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_1 : casesPQ 48 24 9 1 = (tableCodes caseCodes48T 9 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_2 : casesPQ 48 24 9 2 = (tableCodes caseCodes48T 9 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_3 : casesPQ 48 24 9 3 = (tableCodes caseCodes48T 9 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_4 : casesPQ 48 24 9 4 = (tableCodes caseCodes48T 9 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_5 : casesPQ 48 24 9 5 = (tableCodes caseCodes48T 9 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_6 : casesPQ 48 24 9 6 = (tableCodes caseCodes48T 9 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_7 : casesPQ 48 24 9 7 = (tableCodes caseCodes48T 9 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_8 : casesPQ 48 24 9 8 = (tableCodes caseCodes48T 9 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_9 : casesPQ 48 24 9 9 = (tableCodes caseCodes48T 9 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_10 : casesPQ 48 24 9 10 = (tableCodes caseCodes48T 9 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_11 : casesPQ 48 24 9 11 = (tableCodes caseCodes48T 9 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_12 : casesPQ 48 24 9 12 = (tableCodes caseCodes48T 9 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_13 : casesPQ 48 24 9 13 = (tableCodes caseCodes48T 9 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_14 : casesPQ 48 24 9 14 = (tableCodes caseCodes48T 9 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_9_15 : casesPQ 48 24 9 15 = (tableCodes caseCodes48T 9 15).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_0 : casesPQ 48 24 10 0 = (tableCodes caseCodes48T 10 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_1 : casesPQ 48 24 10 1 = (tableCodes caseCodes48T 10 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_2 : casesPQ 48 24 10 2 = (tableCodes caseCodes48T 10 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_3 : casesPQ 48 24 10 3 = (tableCodes caseCodes48T 10 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_4 : casesPQ 48 24 10 4 = (tableCodes caseCodes48T 10 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_5 : casesPQ 48 24 10 5 = (tableCodes caseCodes48T 10 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_6 : casesPQ 48 24 10 6 = (tableCodes caseCodes48T 10 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_7 : casesPQ 48 24 10 7 = (tableCodes caseCodes48T 10 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_8 : casesPQ 48 24 10 8 = (tableCodes caseCodes48T 10 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_9 : casesPQ 48 24 10 9 = (tableCodes caseCodes48T 10 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_10 : casesPQ 48 24 10 10 = (tableCodes caseCodes48T 10 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_11 : casesPQ 48 24 10 11 = (tableCodes caseCodes48T 10 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_12 : casesPQ 48 24 10 12 = (tableCodes caseCodes48T 10 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_13 : casesPQ 48 24 10 13 = (tableCodes caseCodes48T 10 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_10_14 : casesPQ 48 24 10 14 = (tableCodes caseCodes48T 10 14).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_0 : casesPQ 48 24 11 0 = (tableCodes caseCodes48T 11 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_1 : casesPQ 48 24 11 1 = (tableCodes caseCodes48T 11 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_2 : casesPQ 48 24 11 2 = (tableCodes caseCodes48T 11 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_3 : casesPQ 48 24 11 3 = (tableCodes caseCodes48T 11 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_4 : casesPQ 48 24 11 4 = (tableCodes caseCodes48T 11 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_5 : casesPQ 48 24 11 5 = (tableCodes caseCodes48T 11 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_6 : casesPQ 48 24 11 6 = (tableCodes caseCodes48T 11 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_7 : casesPQ 48 24 11 7 = (tableCodes caseCodes48T 11 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_8 : casesPQ 48 24 11 8 = (tableCodes caseCodes48T 11 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_9 : casesPQ 48 24 11 9 = (tableCodes caseCodes48T 11 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_10 : casesPQ 48 24 11 10 = (tableCodes caseCodes48T 11 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_11 : casesPQ 48 24 11 11 = (tableCodes caseCodes48T 11 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_12 : casesPQ 48 24 11 12 = (tableCodes caseCodes48T 11 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_11_13 : casesPQ 48 24 11 13 = (tableCodes caseCodes48T 11 13).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_0 : casesPQ 48 24 12 0 = (tableCodes caseCodes48T 12 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_1 : casesPQ 48 24 12 1 = (tableCodes caseCodes48T 12 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_2 : casesPQ 48 24 12 2 = (tableCodes caseCodes48T 12 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_3 : casesPQ 48 24 12 3 = (tableCodes caseCodes48T 12 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_4 : casesPQ 48 24 12 4 = (tableCodes caseCodes48T 12 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_5 : casesPQ 48 24 12 5 = (tableCodes caseCodes48T 12 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_6 : casesPQ 48 24 12 6 = (tableCodes caseCodes48T 12 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_7 : casesPQ 48 24 12 7 = (tableCodes caseCodes48T 12 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_8 : casesPQ 48 24 12 8 = (tableCodes caseCodes48T 12 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_9 : casesPQ 48 24 12 9 = (tableCodes caseCodes48T 12 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_10 : casesPQ 48 24 12 10 = (tableCodes caseCodes48T 12 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_11 : casesPQ 48 24 12 11 = (tableCodes caseCodes48T 12 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_12_12 : casesPQ 48 24 12 12 = (tableCodes caseCodes48T 12 12).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_0 : casesPQ 48 24 13 0 = (tableCodes caseCodes48T 13 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_1 : casesPQ 48 24 13 1 = (tableCodes caseCodes48T 13 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_2 : casesPQ 48 24 13 2 = (tableCodes caseCodes48T 13 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_3 : casesPQ 48 24 13 3 = (tableCodes caseCodes48T 13 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_4 : casesPQ 48 24 13 4 = (tableCodes caseCodes48T 13 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_5 : casesPQ 48 24 13 5 = (tableCodes caseCodes48T 13 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_6 : casesPQ 48 24 13 6 = (tableCodes caseCodes48T 13 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_7 : casesPQ 48 24 13 7 = (tableCodes caseCodes48T 13 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_8 : casesPQ 48 24 13 8 = (tableCodes caseCodes48T 13 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_9 : casesPQ 48 24 13 9 = (tableCodes caseCodes48T 13 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_10 : casesPQ 48 24 13 10 = (tableCodes caseCodes48T 13 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_13_11 : casesPQ 48 24 13 11 = (tableCodes caseCodes48T 13 11).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_0 : casesPQ 48 24 14 0 = (tableCodes caseCodes48T 14 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_1 : casesPQ 48 24 14 1 = (tableCodes caseCodes48T 14 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_2 : casesPQ 48 24 14 2 = (tableCodes caseCodes48T 14 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_3 : casesPQ 48 24 14 3 = (tableCodes caseCodes48T 14 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_4 : casesPQ 48 24 14 4 = (tableCodes caseCodes48T 14 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_5 : casesPQ 48 24 14 5 = (tableCodes caseCodes48T 14 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_6 : casesPQ 48 24 14 6 = (tableCodes caseCodes48T 14 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_7 : casesPQ 48 24 14 7 = (tableCodes caseCodes48T 14 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_8 : casesPQ 48 24 14 8 = (tableCodes caseCodes48T 14 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_9 : casesPQ 48 24 14 9 = (tableCodes caseCodes48T 14 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_14_10 : casesPQ 48 24 14 10 = (tableCodes caseCodes48T 14 10).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_0 : casesPQ 48 24 15 0 = (tableCodes caseCodes48T 15 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_1 : casesPQ 48 24 15 1 = (tableCodes caseCodes48T 15 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_2 : casesPQ 48 24 15 2 = (tableCodes caseCodes48T 15 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_3 : casesPQ 48 24 15 3 = (tableCodes caseCodes48T 15 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_4 : casesPQ 48 24 15 4 = (tableCodes caseCodes48T 15 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_5 : casesPQ 48 24 15 5 = (tableCodes caseCodes48T 15 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_6 : casesPQ 48 24 15 6 = (tableCodes caseCodes48T 15 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_7 : casesPQ 48 24 15 7 = (tableCodes caseCodes48T 15 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_8 : casesPQ 48 24 15 8 = (tableCodes caseCodes48T 15 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_15_9 : casesPQ 48 24 15 9 = (tableCodes caseCodes48T 15 9).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_0 : casesPQ 48 24 16 0 = (tableCodes caseCodes48T 16 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_1 : casesPQ 48 24 16 1 = (tableCodes caseCodes48T 16 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_2 : casesPQ 48 24 16 2 = (tableCodes caseCodes48T 16 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_3 : casesPQ 48 24 16 3 = (tableCodes caseCodes48T 16 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_4 : casesPQ 48 24 16 4 = (tableCodes caseCodes48T 16 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_5 : casesPQ 48 24 16 5 = (tableCodes caseCodes48T 16 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_6 : casesPQ 48 24 16 6 = (tableCodes caseCodes48T 16 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_7 : casesPQ 48 24 16 7 = (tableCodes caseCodes48T 16 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_16_8 : casesPQ 48 24 16 8 = (tableCodes caseCodes48T 16 8).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_0 : casesPQ 48 24 17 0 = (tableCodes caseCodes48T 17 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_1 : casesPQ 48 24 17 1 = (tableCodes caseCodes48T 17 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_2 : casesPQ 48 24 17 2 = (tableCodes caseCodes48T 17 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_3 : casesPQ 48 24 17 3 = (tableCodes caseCodes48T 17 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_4 : casesPQ 48 24 17 4 = (tableCodes caseCodes48T 17 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_5 : casesPQ 48 24 17 5 = (tableCodes caseCodes48T 17 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_6 : casesPQ 48 24 17 6 = (tableCodes caseCodes48T 17 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_17_7 : casesPQ 48 24 17 7 = (tableCodes caseCodes48T 17 7).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_18_0 : casesPQ 48 24 18 0 = (tableCodes caseCodes48T 18 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_18_1 : casesPQ 48 24 18 1 = (tableCodes caseCodes48T 18 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_18_2 : casesPQ 48 24 18 2 = (tableCodes caseCodes48T 18 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_18_3 : casesPQ 48 24 18 3 = (tableCodes caseCodes48T 18 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_18_4 : casesPQ 48 24 18 4 = (tableCodes caseCodes48T 18 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_18_5 : casesPQ 48 24 18 5 = (tableCodes caseCodes48T 18 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_18_6 : casesPQ 48 24 18 6 = (tableCodes caseCodes48T 18 6).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_19_0 : casesPQ 48 24 19 0 = (tableCodes caseCodes48T 19 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_19_1 : casesPQ 48 24 19 1 = (tableCodes caseCodes48T 19 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_19_2 : casesPQ 48 24 19 2 = (tableCodes caseCodes48T 19 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_19_3 : casesPQ 48 24 19 3 = (tableCodes caseCodes48T 19 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_19_4 : casesPQ 48 24 19 4 = (tableCodes caseCodes48T 19 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_19_5 : casesPQ 48 24 19 5 = (tableCodes caseCodes48T 19 5).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_20_0 : casesPQ 48 24 20 0 = (tableCodes caseCodes48T 20 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_20_1 : casesPQ 48 24 20 1 = (tableCodes caseCodes48T 20 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_20_2 : casesPQ 48 24 20 2 = (tableCodes caseCodes48T 20 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_20_3 : casesPQ 48 24 20 3 = (tableCodes caseCodes48T 20 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_20_4 : casesPQ 48 24 20 4 = (tableCodes caseCodes48T 20 4).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_21_0 : casesPQ 48 24 21 0 = (tableCodes caseCodes48T 21 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_21_1 : casesPQ 48 24 21 1 = (tableCodes caseCodes48T 21 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_21_2 : casesPQ 48 24 21 2 = (tableCodes caseCodes48T 21 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_21_3 : casesPQ 48 24 21 3 = (tableCodes caseCodes48T 21 3).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_22_0 : casesPQ 48 24 22 0 = (tableCodes caseCodes48T 22 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_22_1 : casesPQ 48 24 22 1 = (tableCodes caseCodes48T 22 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_22_2 : casesPQ 48 24 22 2 = (tableCodes caseCodes48T 22 2).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_23_0 : casesPQ 48 24 23 0 = (tableCodes caseCodes48T 23 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_23_1 : casesPQ 48 24 23 1 = (tableCodes caseCodes48T 23 1).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem piece48_24_0 : casesPQ 48 24 24 0 = (tableCodes caseCodes48T 24 0).map Case.ofCode := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **The case list `L(48, 24)` is the decoded table of the run** (assembled from the pieces). -/
theorem enumCases_48_24_table : enumCases 48 24 = (tableList 24 caseCodes48T).map Case.ofCode := by
  refine enumCases_eq_table ?_
  rw [marginPairs_24]
  exact List.forall_mem_cons.2 ⟨piece48_0_0,
    List.forall_mem_cons.2 ⟨piece48_0_1,
    List.forall_mem_cons.2 ⟨piece48_0_2,
    List.forall_mem_cons.2 ⟨piece48_0_3,
    List.forall_mem_cons.2 ⟨piece48_0_4,
    List.forall_mem_cons.2 ⟨piece48_0_5,
    List.forall_mem_cons.2 ⟨piece48_0_6,
    List.forall_mem_cons.2 ⟨piece48_0_7,
    List.forall_mem_cons.2 ⟨piece48_0_8,
    List.forall_mem_cons.2 ⟨piece48_0_9,
    List.forall_mem_cons.2 ⟨piece48_0_10,
    List.forall_mem_cons.2 ⟨piece48_0_11,
    List.forall_mem_cons.2 ⟨piece48_0_12,
    List.forall_mem_cons.2 ⟨piece48_0_13,
    List.forall_mem_cons.2 ⟨piece48_0_14,
    List.forall_mem_cons.2 ⟨piece48_0_15,
    List.forall_mem_cons.2 ⟨piece48_0_16,
    List.forall_mem_cons.2 ⟨piece48_0_17,
    List.forall_mem_cons.2 ⟨piece48_0_18,
    List.forall_mem_cons.2 ⟨piece48_0_19,
    List.forall_mem_cons.2 ⟨piece48_0_20,
    List.forall_mem_cons.2 ⟨piece48_0_21,
    List.forall_mem_cons.2 ⟨piece48_0_22,
    List.forall_mem_cons.2 ⟨piece48_0_23,
    List.forall_mem_cons.2 ⟨piece48_0_24,
    List.forall_mem_cons.2 ⟨piece48_1_0,
    List.forall_mem_cons.2 ⟨piece48_1_1,
    List.forall_mem_cons.2 ⟨piece48_1_2,
    List.forall_mem_cons.2 ⟨piece48_1_3,
    List.forall_mem_cons.2 ⟨piece48_1_4,
    List.forall_mem_cons.2 ⟨piece48_1_5,
    List.forall_mem_cons.2 ⟨piece48_1_6,
    List.forall_mem_cons.2 ⟨piece48_1_7,
    List.forall_mem_cons.2 ⟨piece48_1_8,
    List.forall_mem_cons.2 ⟨piece48_1_9,
    List.forall_mem_cons.2 ⟨piece48_1_10,
    List.forall_mem_cons.2 ⟨piece48_1_11,
    List.forall_mem_cons.2 ⟨piece48_1_12,
    List.forall_mem_cons.2 ⟨piece48_1_13,
    List.forall_mem_cons.2 ⟨piece48_1_14,
    List.forall_mem_cons.2 ⟨piece48_1_15,
    List.forall_mem_cons.2 ⟨piece48_1_16,
    List.forall_mem_cons.2 ⟨piece48_1_17,
    List.forall_mem_cons.2 ⟨piece48_1_18,
    List.forall_mem_cons.2 ⟨piece48_1_19,
    List.forall_mem_cons.2 ⟨piece48_1_20,
    List.forall_mem_cons.2 ⟨piece48_1_21,
    List.forall_mem_cons.2 ⟨piece48_1_22,
    List.forall_mem_cons.2 ⟨piece48_1_23,
    List.forall_mem_cons.2 ⟨piece48_2_0,
    List.forall_mem_cons.2 ⟨piece48_2_1,
    List.forall_mem_cons.2 ⟨piece48_2_2,
    List.forall_mem_cons.2 ⟨piece48_2_3,
    List.forall_mem_cons.2 ⟨piece48_2_4,
    List.forall_mem_cons.2 ⟨piece48_2_5,
    List.forall_mem_cons.2 ⟨piece48_2_6,
    List.forall_mem_cons.2 ⟨piece48_2_7,
    List.forall_mem_cons.2 ⟨piece48_2_8,
    List.forall_mem_cons.2 ⟨piece48_2_9,
    List.forall_mem_cons.2 ⟨piece48_2_10,
    List.forall_mem_cons.2 ⟨piece48_2_11,
    List.forall_mem_cons.2 ⟨piece48_2_12,
    List.forall_mem_cons.2 ⟨piece48_2_13,
    List.forall_mem_cons.2 ⟨piece48_2_14,
    List.forall_mem_cons.2 ⟨piece48_2_15,
    List.forall_mem_cons.2 ⟨piece48_2_16,
    List.forall_mem_cons.2 ⟨piece48_2_17,
    List.forall_mem_cons.2 ⟨piece48_2_18,
    List.forall_mem_cons.2 ⟨piece48_2_19,
    List.forall_mem_cons.2 ⟨piece48_2_20,
    List.forall_mem_cons.2 ⟨piece48_2_21,
    List.forall_mem_cons.2 ⟨piece48_2_22,
    List.forall_mem_cons.2 ⟨piece48_3_0,
    List.forall_mem_cons.2 ⟨piece48_3_1,
    List.forall_mem_cons.2 ⟨piece48_3_2,
    List.forall_mem_cons.2 ⟨piece48_3_3,
    List.forall_mem_cons.2 ⟨piece48_3_4,
    List.forall_mem_cons.2 ⟨piece48_3_5,
    List.forall_mem_cons.2 ⟨piece48_3_6,
    List.forall_mem_cons.2 ⟨piece48_3_7,
    List.forall_mem_cons.2 ⟨piece48_3_8,
    List.forall_mem_cons.2 ⟨piece48_3_9,
    List.forall_mem_cons.2 ⟨piece48_3_10,
    List.forall_mem_cons.2 ⟨piece48_3_11,
    List.forall_mem_cons.2 ⟨piece48_3_12,
    List.forall_mem_cons.2 ⟨piece48_3_13,
    List.forall_mem_cons.2 ⟨piece48_3_14,
    List.forall_mem_cons.2 ⟨piece48_3_15,
    List.forall_mem_cons.2 ⟨piece48_3_16,
    List.forall_mem_cons.2 ⟨piece48_3_17,
    List.forall_mem_cons.2 ⟨piece48_3_18,
    List.forall_mem_cons.2 ⟨piece48_3_19,
    List.forall_mem_cons.2 ⟨piece48_3_20,
    List.forall_mem_cons.2 ⟨piece48_3_21,
    List.forall_mem_cons.2 ⟨piece48_4_0,
    List.forall_mem_cons.2 ⟨piece48_4_1,
    List.forall_mem_cons.2 ⟨piece48_4_2,
    List.forall_mem_cons.2 ⟨piece48_4_3,
    List.forall_mem_cons.2 ⟨piece48_4_4,
    List.forall_mem_cons.2 ⟨piece48_4_5,
    List.forall_mem_cons.2 ⟨piece48_4_6,
    List.forall_mem_cons.2 ⟨piece48_4_7,
    List.forall_mem_cons.2 ⟨piece48_4_8,
    List.forall_mem_cons.2 ⟨piece48_4_9,
    List.forall_mem_cons.2 ⟨piece48_4_10,
    List.forall_mem_cons.2 ⟨piece48_4_11,
    List.forall_mem_cons.2 ⟨piece48_4_12,
    List.forall_mem_cons.2 ⟨piece48_4_13,
    List.forall_mem_cons.2 ⟨piece48_4_14,
    List.forall_mem_cons.2 ⟨piece48_4_15,
    List.forall_mem_cons.2 ⟨piece48_4_16,
    List.forall_mem_cons.2 ⟨piece48_4_17,
    List.forall_mem_cons.2 ⟨piece48_4_18,
    List.forall_mem_cons.2 ⟨piece48_4_19,
    List.forall_mem_cons.2 ⟨piece48_4_20,
    List.forall_mem_cons.2 ⟨piece48_5_0,
    List.forall_mem_cons.2 ⟨piece48_5_1,
    List.forall_mem_cons.2 ⟨piece48_5_2,
    List.forall_mem_cons.2 ⟨piece48_5_3,
    List.forall_mem_cons.2 ⟨piece48_5_4,
    List.forall_mem_cons.2 ⟨piece48_5_5,
    List.forall_mem_cons.2 ⟨piece48_5_6,
    List.forall_mem_cons.2 ⟨piece48_5_7,
    List.forall_mem_cons.2 ⟨piece48_5_8,
    List.forall_mem_cons.2 ⟨piece48_5_9,
    List.forall_mem_cons.2 ⟨piece48_5_10,
    List.forall_mem_cons.2 ⟨piece48_5_11,
    List.forall_mem_cons.2 ⟨piece48_5_12,
    List.forall_mem_cons.2 ⟨piece48_5_13,
    List.forall_mem_cons.2 ⟨piece48_5_14,
    List.forall_mem_cons.2 ⟨piece48_5_15,
    List.forall_mem_cons.2 ⟨piece48_5_16,
    List.forall_mem_cons.2 ⟨piece48_5_17,
    List.forall_mem_cons.2 ⟨piece48_5_18,
    List.forall_mem_cons.2 ⟨piece48_5_19,
    List.forall_mem_cons.2 ⟨piece48_6_0,
    List.forall_mem_cons.2 ⟨piece48_6_1,
    List.forall_mem_cons.2 ⟨piece48_6_2,
    List.forall_mem_cons.2 ⟨piece48_6_3,
    List.forall_mem_cons.2 ⟨piece48_6_4,
    List.forall_mem_cons.2 ⟨piece48_6_5,
    List.forall_mem_cons.2 ⟨piece48_6_6,
    List.forall_mem_cons.2 ⟨piece48_6_7,
    List.forall_mem_cons.2 ⟨piece48_6_8,
    List.forall_mem_cons.2 ⟨piece48_6_9,
    List.forall_mem_cons.2 ⟨piece48_6_10,
    List.forall_mem_cons.2 ⟨piece48_6_11,
    List.forall_mem_cons.2 ⟨piece48_6_12,
    List.forall_mem_cons.2 ⟨piece48_6_13,
    List.forall_mem_cons.2 ⟨piece48_6_14,
    List.forall_mem_cons.2 ⟨piece48_6_15,
    List.forall_mem_cons.2 ⟨piece48_6_16,
    List.forall_mem_cons.2 ⟨piece48_6_17,
    List.forall_mem_cons.2 ⟨piece48_6_18,
    List.forall_mem_cons.2 ⟨piece48_7_0,
    List.forall_mem_cons.2 ⟨piece48_7_1,
    List.forall_mem_cons.2 ⟨piece48_7_2,
    List.forall_mem_cons.2 ⟨piece48_7_3,
    List.forall_mem_cons.2 ⟨piece48_7_4,
    List.forall_mem_cons.2 ⟨piece48_7_5,
    List.forall_mem_cons.2 ⟨piece48_7_6,
    List.forall_mem_cons.2 ⟨piece48_7_7,
    List.forall_mem_cons.2 ⟨piece48_7_8,
    List.forall_mem_cons.2 ⟨piece48_7_9,
    List.forall_mem_cons.2 ⟨piece48_7_10,
    List.forall_mem_cons.2 ⟨piece48_7_11,
    List.forall_mem_cons.2 ⟨piece48_7_12,
    List.forall_mem_cons.2 ⟨piece48_7_13,
    List.forall_mem_cons.2 ⟨piece48_7_14,
    List.forall_mem_cons.2 ⟨piece48_7_15,
    List.forall_mem_cons.2 ⟨piece48_7_16,
    List.forall_mem_cons.2 ⟨piece48_7_17,
    List.forall_mem_cons.2 ⟨piece48_8_0,
    List.forall_mem_cons.2 ⟨piece48_8_1,
    List.forall_mem_cons.2 ⟨piece48_8_2,
    List.forall_mem_cons.2 ⟨piece48_8_3,
    List.forall_mem_cons.2 ⟨piece48_8_4,
    List.forall_mem_cons.2 ⟨piece48_8_5,
    List.forall_mem_cons.2 ⟨piece48_8_6,
    List.forall_mem_cons.2 ⟨piece48_8_7,
    List.forall_mem_cons.2 ⟨piece48_8_8,
    List.forall_mem_cons.2 ⟨piece48_8_9,
    List.forall_mem_cons.2 ⟨piece48_8_10,
    List.forall_mem_cons.2 ⟨piece48_8_11,
    List.forall_mem_cons.2 ⟨piece48_8_12,
    List.forall_mem_cons.2 ⟨piece48_8_13,
    List.forall_mem_cons.2 ⟨piece48_8_14,
    List.forall_mem_cons.2 ⟨piece48_8_15,
    List.forall_mem_cons.2 ⟨piece48_8_16,
    List.forall_mem_cons.2 ⟨piece48_9_0,
    List.forall_mem_cons.2 ⟨piece48_9_1,
    List.forall_mem_cons.2 ⟨piece48_9_2,
    List.forall_mem_cons.2 ⟨piece48_9_3,
    List.forall_mem_cons.2 ⟨piece48_9_4,
    List.forall_mem_cons.2 ⟨piece48_9_5,
    List.forall_mem_cons.2 ⟨piece48_9_6,
    List.forall_mem_cons.2 ⟨piece48_9_7,
    List.forall_mem_cons.2 ⟨piece48_9_8,
    List.forall_mem_cons.2 ⟨piece48_9_9,
    List.forall_mem_cons.2 ⟨piece48_9_10,
    List.forall_mem_cons.2 ⟨piece48_9_11,
    List.forall_mem_cons.2 ⟨piece48_9_12,
    List.forall_mem_cons.2 ⟨piece48_9_13,
    List.forall_mem_cons.2 ⟨piece48_9_14,
    List.forall_mem_cons.2 ⟨piece48_9_15,
    List.forall_mem_cons.2 ⟨piece48_10_0,
    List.forall_mem_cons.2 ⟨piece48_10_1,
    List.forall_mem_cons.2 ⟨piece48_10_2,
    List.forall_mem_cons.2 ⟨piece48_10_3,
    List.forall_mem_cons.2 ⟨piece48_10_4,
    List.forall_mem_cons.2 ⟨piece48_10_5,
    List.forall_mem_cons.2 ⟨piece48_10_6,
    List.forall_mem_cons.2 ⟨piece48_10_7,
    List.forall_mem_cons.2 ⟨piece48_10_8,
    List.forall_mem_cons.2 ⟨piece48_10_9,
    List.forall_mem_cons.2 ⟨piece48_10_10,
    List.forall_mem_cons.2 ⟨piece48_10_11,
    List.forall_mem_cons.2 ⟨piece48_10_12,
    List.forall_mem_cons.2 ⟨piece48_10_13,
    List.forall_mem_cons.2 ⟨piece48_10_14,
    List.forall_mem_cons.2 ⟨piece48_11_0,
    List.forall_mem_cons.2 ⟨piece48_11_1,
    List.forall_mem_cons.2 ⟨piece48_11_2,
    List.forall_mem_cons.2 ⟨piece48_11_3,
    List.forall_mem_cons.2 ⟨piece48_11_4,
    List.forall_mem_cons.2 ⟨piece48_11_5,
    List.forall_mem_cons.2 ⟨piece48_11_6,
    List.forall_mem_cons.2 ⟨piece48_11_7,
    List.forall_mem_cons.2 ⟨piece48_11_8,
    List.forall_mem_cons.2 ⟨piece48_11_9,
    List.forall_mem_cons.2 ⟨piece48_11_10,
    List.forall_mem_cons.2 ⟨piece48_11_11,
    List.forall_mem_cons.2 ⟨piece48_11_12,
    List.forall_mem_cons.2 ⟨piece48_11_13,
    List.forall_mem_cons.2 ⟨piece48_12_0,
    List.forall_mem_cons.2 ⟨piece48_12_1,
    List.forall_mem_cons.2 ⟨piece48_12_2,
    List.forall_mem_cons.2 ⟨piece48_12_3,
    List.forall_mem_cons.2 ⟨piece48_12_4,
    List.forall_mem_cons.2 ⟨piece48_12_5,
    List.forall_mem_cons.2 ⟨piece48_12_6,
    List.forall_mem_cons.2 ⟨piece48_12_7,
    List.forall_mem_cons.2 ⟨piece48_12_8,
    List.forall_mem_cons.2 ⟨piece48_12_9,
    List.forall_mem_cons.2 ⟨piece48_12_10,
    List.forall_mem_cons.2 ⟨piece48_12_11,
    List.forall_mem_cons.2 ⟨piece48_12_12,
    List.forall_mem_cons.2 ⟨piece48_13_0,
    List.forall_mem_cons.2 ⟨piece48_13_1,
    List.forall_mem_cons.2 ⟨piece48_13_2,
    List.forall_mem_cons.2 ⟨piece48_13_3,
    List.forall_mem_cons.2 ⟨piece48_13_4,
    List.forall_mem_cons.2 ⟨piece48_13_5,
    List.forall_mem_cons.2 ⟨piece48_13_6,
    List.forall_mem_cons.2 ⟨piece48_13_7,
    List.forall_mem_cons.2 ⟨piece48_13_8,
    List.forall_mem_cons.2 ⟨piece48_13_9,
    List.forall_mem_cons.2 ⟨piece48_13_10,
    List.forall_mem_cons.2 ⟨piece48_13_11,
    List.forall_mem_cons.2 ⟨piece48_14_0,
    List.forall_mem_cons.2 ⟨piece48_14_1,
    List.forall_mem_cons.2 ⟨piece48_14_2,
    List.forall_mem_cons.2 ⟨piece48_14_3,
    List.forall_mem_cons.2 ⟨piece48_14_4,
    List.forall_mem_cons.2 ⟨piece48_14_5,
    List.forall_mem_cons.2 ⟨piece48_14_6,
    List.forall_mem_cons.2 ⟨piece48_14_7,
    List.forall_mem_cons.2 ⟨piece48_14_8,
    List.forall_mem_cons.2 ⟨piece48_14_9,
    List.forall_mem_cons.2 ⟨piece48_14_10,
    List.forall_mem_cons.2 ⟨piece48_15_0,
    List.forall_mem_cons.2 ⟨piece48_15_1,
    List.forall_mem_cons.2 ⟨piece48_15_2,
    List.forall_mem_cons.2 ⟨piece48_15_3,
    List.forall_mem_cons.2 ⟨piece48_15_4,
    List.forall_mem_cons.2 ⟨piece48_15_5,
    List.forall_mem_cons.2 ⟨piece48_15_6,
    List.forall_mem_cons.2 ⟨piece48_15_7,
    List.forall_mem_cons.2 ⟨piece48_15_8,
    List.forall_mem_cons.2 ⟨piece48_15_9,
    List.forall_mem_cons.2 ⟨piece48_16_0,
    List.forall_mem_cons.2 ⟨piece48_16_1,
    List.forall_mem_cons.2 ⟨piece48_16_2,
    List.forall_mem_cons.2 ⟨piece48_16_3,
    List.forall_mem_cons.2 ⟨piece48_16_4,
    List.forall_mem_cons.2 ⟨piece48_16_5,
    List.forall_mem_cons.2 ⟨piece48_16_6,
    List.forall_mem_cons.2 ⟨piece48_16_7,
    List.forall_mem_cons.2 ⟨piece48_16_8,
    List.forall_mem_cons.2 ⟨piece48_17_0,
    List.forall_mem_cons.2 ⟨piece48_17_1,
    List.forall_mem_cons.2 ⟨piece48_17_2,
    List.forall_mem_cons.2 ⟨piece48_17_3,
    List.forall_mem_cons.2 ⟨piece48_17_4,
    List.forall_mem_cons.2 ⟨piece48_17_5,
    List.forall_mem_cons.2 ⟨piece48_17_6,
    List.forall_mem_cons.2 ⟨piece48_17_7,
    List.forall_mem_cons.2 ⟨piece48_18_0,
    List.forall_mem_cons.2 ⟨piece48_18_1,
    List.forall_mem_cons.2 ⟨piece48_18_2,
    List.forall_mem_cons.2 ⟨piece48_18_3,
    List.forall_mem_cons.2 ⟨piece48_18_4,
    List.forall_mem_cons.2 ⟨piece48_18_5,
    List.forall_mem_cons.2 ⟨piece48_18_6,
    List.forall_mem_cons.2 ⟨piece48_19_0,
    List.forall_mem_cons.2 ⟨piece48_19_1,
    List.forall_mem_cons.2 ⟨piece48_19_2,
    List.forall_mem_cons.2 ⟨piece48_19_3,
    List.forall_mem_cons.2 ⟨piece48_19_4,
    List.forall_mem_cons.2 ⟨piece48_19_5,
    List.forall_mem_cons.2 ⟨piece48_20_0,
    List.forall_mem_cons.2 ⟨piece48_20_1,
    List.forall_mem_cons.2 ⟨piece48_20_2,
    List.forall_mem_cons.2 ⟨piece48_20_3,
    List.forall_mem_cons.2 ⟨piece48_20_4,
    List.forall_mem_cons.2 ⟨piece48_21_0,
    List.forall_mem_cons.2 ⟨piece48_21_1,
    List.forall_mem_cons.2 ⟨piece48_21_2,
    List.forall_mem_cons.2 ⟨piece48_21_3,
    List.forall_mem_cons.2 ⟨piece48_22_0,
    List.forall_mem_cons.2 ⟨piece48_22_1,
    List.forall_mem_cons.2 ⟨piece48_22_2,
    List.forall_mem_cons.2 ⟨piece48_23_0,
    List.forall_mem_cons.2 ⟨piece48_23_1,
    List.forall_mem_cons.2 ⟨piece48_24_0,
    List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end QueenDom
