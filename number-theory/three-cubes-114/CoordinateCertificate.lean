module

public import ForcedCoordinates

/-! Kernel-checkable factor and divisor certificates for the 256 signed coordinates
with `10^19 < |z| ≤ 10^19 + 128`. The local congruences dispose of the coordinates
outside `admissible`. The remaining coordinates use complete prime factorizations.
Primality witnesses below are shared between factorizations. -/

public section

namespace ThreeCubes114.CoordinateCertificate

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem prime_2 : Nat.Prime 2 := by decide

private theorem prime_3 : Nat.Prime 3 := by decide

private theorem prime_5 : Nat.Prime 5 := by decide

private theorem prime_7 : Nat.Prime 7 := by decide

private theorem prime_11 : Nat.Prime 11 := by decide

private theorem prime_13 : Nat.Prime 13 := by decide

private theorem prime_17 : Nat.Prime 17 := by decide

private theorem prime_19 : Nat.Prime 19 := by decide

private theorem prime_23 : Nat.Prime 23 := by decide

private theorem prime_29 : Nat.Prime 29 := by decide

private theorem prime_31 : Nat.Prime 31 := by decide

private theorem prime_37 : Nat.Prime 37 := by decide

private theorem prime_41 : Nat.Prime 41 := by decide

private theorem prime_43 : Nat.Prime 43 := by decide

private theorem prime_47 : Nat.Prime 47 := by decide

private theorem prime_53 : Nat.Prime 53 := by decide

private theorem prime_59 : Nat.Prime 59 := by decide

private theorem prime_61 : Nat.Prime 61 := by decide

private theorem prime_67 : Nat.Prime 67 := by decide

private theorem prime_71 : Nat.Prime 71 := by decide

private theorem prime_73 : Nat.Prime 73 := by decide

private theorem prime_79 : Nat.Prime 79 := by decide

private theorem prime_83 : Nat.Prime 83 := by decide

private theorem prime_89 : Nat.Prime 89 := by decide

private theorem prime_97 : Nat.Prime 97 := by decide

private theorem prime_101 : Nat.Prime 101 := by decide

private theorem prime_103 : Nat.Prime 103 := by decide

private theorem prime_107 : Nat.Prime 107 := by decide

private theorem prime_109 : Nat.Prime 109 := by decide

private theorem prime_113 : Nat.Prime 113 := by decide

private theorem prime_127 : Nat.Prime 127 := by decide

private theorem prime_131 : Nat.Prime 131 := by decide

private theorem prime_137 : Nat.Prime 137 := by decide

private theorem prime_139 : Nat.Prime 139 := by decide

private theorem prime_149 : Nat.Prime 149 := by decide

private theorem prime_151 : Nat.Prime 151 := by decide

private theorem prime_157 : Nat.Prime 157 := by decide

private theorem prime_163 : Nat.Prime 163 := by decide

private theorem prime_167 : Nat.Prime 167 := by decide

private theorem prime_173 : Nat.Prime 173 := by decide

private theorem prime_179 : Nat.Prime 179 := by decide

private theorem prime_181 : Nat.Prime 181 := by decide

private theorem prime_191 : Nat.Prime 191 := by decide

private theorem prime_193 : Nat.Prime 193 := by decide

private theorem prime_197 : Nat.Prime 197 := by decide

private theorem prime_199 : Nat.Prime 199 := by decide

private theorem prime_211 : Nat.Prime 211 := by decide

private theorem prime_223 : Nat.Prime 223 := by decide

private theorem prime_227 : Nat.Prime 227 := by decide

private theorem prime_229 : Nat.Prime 229 := by decide

private theorem prime_233 : Nat.Prime 233 := by decide

private theorem prime_239 : Nat.Prime 239 := by decide

private theorem prime_241 : Nat.Prime 241 := by decide

private theorem prime_251 : Nat.Prime 251 := by decide

private theorem prime_257 : Nat.Prime 257 := by decide

private theorem prime_263 : Nat.Prime 263 := by decide

private theorem prime_269 : Nat.Prime 269 := by decide

private theorem prime_271 : Nat.Prime 271 := by decide

private theorem prime_277 : Nat.Prime 277 := by decide

private theorem prime_281 : Nat.Prime 281 := by decide

private theorem prime_293 : Nat.Prime 293 := by decide

private theorem prime_307 : Nat.Prime 307 := by decide

private theorem prime_311 : Nat.Prime 311 := by decide

private theorem prime_313 : Nat.Prime 313 := by decide

private theorem prime_317 : Nat.Prime 317 := by decide

private theorem prime_331 : Nat.Prime 331 := by decide

private theorem prime_337 : Nat.Prime 337 := by decide

private theorem prime_347 : Nat.Prime 347 := by decide

private theorem prime_349 : Nat.Prime 349 := by decide

private theorem prime_353 : Nat.Prime 353 := by decide

private theorem prime_359 : Nat.Prime 359 := by decide

private theorem prime_367 : Nat.Prime 367 := by decide

private theorem prime_373 : Nat.Prime 373 := by decide

private theorem prime_379 : Nat.Prime 379 := by decide

private theorem prime_383 : Nat.Prime 383 := by decide

private theorem prime_389 : Nat.Prime 389 := by decide

private theorem prime_397 : Nat.Prime 397 := by decide

private theorem prime_401 : Nat.Prime 401 := by decide

private theorem prime_409 : Nat.Prime 409 := by decide

private theorem prime_419 : Nat.Prime 419 := by decide

private theorem prime_421 : Nat.Prime 421 := by decide

private theorem prime_431 : Nat.Prime 431 := by decide

private theorem prime_433 : Nat.Prime 433 := by decide

private theorem prime_461 : Nat.Prime 461 := by decide

private theorem prime_463 : Nat.Prime 463 := by decide

private theorem prime_479 : Nat.Prime 479 := by decide

private theorem prime_487 : Nat.Prime 487 := by decide

private theorem prime_491 : Nat.Prime 491 := by decide

private theorem prime_499 : Nat.Prime 499 := by decide

private theorem prime_503 : Nat.Prime 503 := by decide

private theorem prime_521 : Nat.Prime 521 := by decide

private theorem prime_523 : Nat.Prime 523 := by decide

private theorem prime_541 : Nat.Prime 541 := by decide

private theorem prime_557 : Nat.Prime 557 := by decide

private theorem prime_563 : Nat.Prime 563 := by decide

private theorem prime_569 : Nat.Prime 569 := by decide

private theorem prime_577 : Nat.Prime 577 := by decide

private theorem prime_599 : Nat.Prime 599 := by decide

private theorem prime_601 : Nat.Prime 601 := by decide

private theorem prime_607 : Nat.Prime 607 := by decide

private theorem prime_613 : Nat.Prime 613 := by decide

private theorem prime_631 : Nat.Prime 631 := by decide

private theorem prime_641 : Nat.Prime 641 := by decide

private theorem prime_653 : Nat.Prime 653 := by decide

private theorem prime_659 : Nat.Prime 659 := by decide

private theorem prime_683 : Nat.Prime 683 := by decide

private theorem prime_691 : Nat.Prime 691 := by decide

private theorem prime_709 : Nat.Prime 709 := by decide

private theorem prime_719 : Nat.Prime 719 := by decide

private theorem prime_727 : Nat.Prime 727 := by decide

private theorem prime_733 : Nat.Prime 733 := by decide

private theorem prime_743 : Nat.Prime 743 := by decide

private theorem prime_761 : Nat.Prime 761 := by decide

private theorem prime_769 : Nat.Prime 769 := by decide

private theorem prime_773 : Nat.Prime 773 := by decide

private theorem prime_797 : Nat.Prime 797 := by decide

private theorem prime_811 : Nat.Prime 811 := by decide

private theorem prime_823 : Nat.Prime 823 := by decide

private theorem prime_859 : Nat.Prime 859 := by decide

private theorem prime_863 : Nat.Prime 863 := by decide

private theorem prime_881 : Nat.Prime 881 := by decide

private theorem prime_907 : Nat.Prime 907 := by decide

private theorem prime_911 : Nat.Prime 911 := by decide

private theorem prime_929 : Nat.Prime 929 := by decide

private theorem prime_941 : Nat.Prime 941 := by decide

private theorem prime_947 : Nat.Prime 947 := by decide

private theorem prime_971 : Nat.Prime 971 := by decide

private theorem prime_977 : Nat.Prime 977 := by decide

private theorem prime_1013 : Nat.Prime 1013 := by decide

private theorem prime_1019 : Nat.Prime 1019 := by decide

private theorem prime_1021 : Nat.Prime 1021 := by decide

private theorem prime_1031 : Nat.Prime 1031 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 103] }])
    [prime_2, prime_5, prime_103]

private theorem prime_1039 : Nat.Prime 1039 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 173] }])
    [prime_2, prime_3, prime_173]

private theorem prime_1051 : Nat.Prime 1051 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 7] }])
    [prime_2, prime_3, prime_5, prime_7]

private theorem prime_1091 : Nat.Prime 1091 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 109] }])
    [prime_2, prime_5, prime_109]

private theorem prime_1093 : Nat.Prime 1093 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13] }])
    [prime_2, prime_3, prime_7, prime_13]

private theorem prime_1103 : Nat.Prime 1103 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 29] }])
    [prime_2, prime_19, prime_29]

private theorem prime_1109 : Nat.Prime 1109 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 277] }])
    [prime_2, prime_277]

private theorem prime_1117 : Nat.Prime 1117 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31] }])
    [prime_2, prime_3, prime_31]

private theorem prime_1123 : Nat.Prime 1123 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 17] }])
    [prime_2, prime_3, prime_11, prime_17]

private theorem prime_1129 : Nat.Prime 1129 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 47] }])
    [prime_2, prime_3, prime_47]

private theorem prime_1153 : Nat.Prime 1153 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3] }])
    [prime_2, prime_3]

private theorem prime_1171 : Nat.Prime 1171 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13] }])
    [prime_2, prime_3, prime_5, prime_13]

private theorem prime_1181 : Nat.Prime 1181 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 59] }])
    [prime_2, prime_5, prime_59]

private theorem prime_1193 : Nat.Prime 1193 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 149] }])
    [prime_2, prime_149]

private theorem prime_1217 : Nat.Prime 1217 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19] }])
    [prime_2, prime_19]

private theorem prime_1223 : Nat.Prime 1223 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 47] }])
    [prime_2, prime_13, prime_47]

private theorem prime_1231 : Nat.Prime 1231 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 41] }])
    [prime_2, prime_3, prime_5, prime_41]

private theorem prime_1259 : Nat.Prime 1259 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 37] }])
    [prime_2, prime_17, prime_37]

private theorem prime_1283 : Nat.Prime 1283 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 641] }])
    [prime_2, prime_641]

private theorem prime_1289 : Nat.Prime 1289 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 23] }])
    [prime_2, prime_7, prime_23]

private theorem prime_1301 : Nat.Prime 1301 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13] }])
    [prime_2, prime_5, prime_13]

private theorem prime_1303 : Nat.Prime 1303 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 31] }])
    [prime_2, prime_3, prime_7, prime_31]

private theorem prime_1307 : Nat.Prime 1307 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 653] }])
    [prime_2, prime_653]

private theorem prime_1321 : Nat.Prime 1321 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11] }])
    [prime_2, prime_3, prime_5, prime_11]

private theorem prime_1381 : Nat.Prime 1381 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 23] }])
    [prime_2, prime_3, prime_5, prime_23]

private theorem prime_1409 : Nat.Prime 1409 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11] }])
    [prime_2, prime_11]

private theorem prime_1423 : Nat.Prime 1423 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 79] }])
    [prime_2, prime_3, prime_79]

private theorem prime_1453 : Nat.Prime 1453 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11] }])
    [prime_2, prime_3, prime_11]

private theorem prime_1471 : Nat.Prime 1471 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7] }])
    [prime_2, prime_3, prime_5, prime_7]

private theorem prime_1481 : Nat.Prime 1481 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 37] }])
    [prime_2, prime_5, prime_37]

private theorem prime_1483 : Nat.Prime 1483 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }])
    [prime_2, prime_3, prime_13, prime_19]

private theorem prime_1487 : Nat.Prime 1487 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 743] }])
    [prime_2, prime_743]

private theorem prime_1499 : Nat.Prime 1499 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 107] }])
    [prime_2, prime_7, prime_107]

private theorem prime_1523 : Nat.Prime 1523 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 761] }])
    [prime_2, prime_761]

private theorem prime_1531 : Nat.Prime 1531 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 17] }])
    [prime_2, prime_3, prime_5, prime_17]

private theorem prime_1543 : Nat.Prime 1543 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 257] }])
    [prime_2, prime_3, prime_257]

private theorem prime_1553 : Nat.Prime 1553 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 97] }])
    [prime_2, prime_97]

private theorem prime_1567 : Nat.Prime 1567 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 29] }])
    [prime_2, prime_3, prime_29]

private theorem prime_1579 : Nat.Prime 1579 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 263] }])
    [prime_2, prime_3, prime_263]

private theorem prime_1601 : Nat.Prime 1601 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5] }])
    [prime_2, prime_5]

private theorem prime_1607 : Nat.Prime 1607 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 73] }])
    [prime_2, prime_11, prime_73]

private theorem prime_1621 : Nat.Prime 1621 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5] }])
    [prime_2, prime_3, prime_5]

private theorem prime_1667 : Nat.Prime 1667 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17] }])
    [prime_2, prime_7, prime_17]

private theorem prime_1693 : Nat.Prime 1693 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 47] }])
    [prime_2, prime_3, prime_47]

private theorem prime_1709 : Nat.Prime 1709 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 61] }])
    [prime_2, prime_7, prime_61]

private theorem prime_1747 : Nat.Prime 1747 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 97] }])
    [prime_2, prime_3, prime_97]

private theorem prime_1777 : Nat.Prime 1777 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 37] }])
    [prime_2, prime_3, prime_37]

private theorem prime_1783 : Nat.Prime 1783 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11] }])
    [prime_2, prime_3, prime_11]

private theorem prime_1801 : Nat.Prime 1801 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5] }])
    [prime_2, prime_3, prime_5]

private theorem prime_1811 : Nat.Prime 1811 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 181] }])
    [prime_2, prime_5, prime_181]

private theorem prime_1873 : Nat.Prime 1873 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13] }])
    [prime_2, prime_3, prime_13]

private theorem prime_1879 : Nat.Prime 1879 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 313] }])
    [prime_2, prime_3, prime_313]

private theorem prime_1889 : Nat.Prime 1889 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 59] }])
    [prime_2, prime_59]

private theorem prime_1901 : Nat.Prime 1901 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19] }])
    [prime_2, prime_5, prime_19]

private theorem prime_1913 : Nat.Prime 1913 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 239] }])
    [prime_2, prime_239]

private theorem prime_1979 : Nat.Prime 1979 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 43] }])
    [prime_2, prime_23, prime_43]

private theorem prime_2027 : Nat.Prime 2027 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1013] }])
    [prime_2, prime_1013]

private theorem prime_2039 : Nat.Prime 2039 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 1019] }])
    [prime_2, prime_1019]

private theorem prime_2063 : Nat.Prime 2063 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1031] }])
    [prime_2, prime_1031]

private theorem prime_2069 : Nat.Prime 2069 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 47] }])
    [prime_2, prime_11, prime_47]

private theorem prime_2081 : Nat.Prime 2081 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13] }])
    [prime_2, prime_5, prime_13]

private theorem prime_2141 : Nat.Prime 2141 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 107] }])
    [prime_2, prime_5, prime_107]

private theorem prime_2153 : Nat.Prime 2153 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 269] }])
    [prime_2, prime_269]

private theorem prime_2179 : Nat.Prime 2179 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }])
    [prime_2, prime_3, prime_11]

private theorem prime_2203 : Nat.Prime 2203 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 367] }])
    [prime_2, prime_3, prime_367]

private theorem prime_2221 : Nat.Prime 2221 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 37] }])
    [prime_2, prime_3, prime_5, prime_37]

private theorem prime_2239 : Nat.Prime 2239 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 373] }])
    [prime_2, prime_3, prime_373]

private theorem prime_2269 : Nat.Prime 2269 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7] }])
    [prime_2, prime_3, prime_7]

private theorem prime_2273 : Nat.Prime 2273 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 71] }])
    [prime_2, prime_71]

private theorem prime_2281 : Nat.Prime 2281 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 19] }])
    [prime_2, prime_3, prime_5, prime_19]

private theorem prime_2333 : Nat.Prime 2333 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 53] }])
    [prime_2, prime_11, prime_53]

private theorem prime_2341 : Nat.Prime 2341 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13] }])
    [prime_2, prime_3, prime_5, prime_13]

private theorem prime_2371 : Nat.Prime 2371 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 79] }])
    [prime_2, prime_3, prime_5, prime_79]

private theorem prime_2437 : Nat.Prime 2437 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 29] }])
    [prime_2, prime_3, prime_7, prime_29]

private theorem prime_2447 : Nat.Prime 2447 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1223] }])
    [prime_2, prime_1223]

private theorem prime_2591 : Nat.Prime 2591 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 37] }])
    [prime_2, prime_5, prime_7, prime_37]

private theorem prime_2593 : Nat.Prime 2593 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3] }])
    [prime_2, prime_3]

private theorem prime_2609 : Nat.Prime 2609 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 163] }])
    [prime_2, prime_163]

private theorem prime_2663 : Nat.Prime 2663 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11] }])
    [prime_2, prime_11]

private theorem prime_2777 : Nat.Prime 2777 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 347] }])
    [prime_2, prime_347]

private theorem prime_2801 : Nat.Prime 2801 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7] }])
    [prime_2, prime_5, prime_7]

private theorem prime_2837 : Nat.Prime 2837 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 709] }])
    [prime_2, prime_709]

private theorem prime_2857 : Nat.Prime 2857 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 7, 17] }])
    [prime_2, prime_3, prime_7, prime_17]

private theorem prime_2971 : Nat.Prime 2971 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 11] }])
    [prime_2, prime_3, prime_5, prime_11]

private theorem prime_2999 : Nat.Prime 2999 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 1499] }])
    [prime_2, prime_1499]

private theorem prime_3163 : Nat.Prime 3163 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 31] }])
    [prime_2, prime_3, prime_17, prime_31]

private theorem prime_3181 : Nat.Prime 3181 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 53] }])
    [prime_2, prime_3, prime_5, prime_53]

private theorem prime_3187 : Nat.Prime 3187 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59] }])
    [prime_2, prime_3, prime_59]

private theorem prime_3221 : Nat.Prime 3221 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 5, 7, 23] }])
    [prime_2, prime_5, prime_7, prime_23]

private theorem prime_3257 : Nat.Prime 3257 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 37] }])
    [prime_2, prime_11, prime_37]

private theorem prime_3301 : Nat.Prime 3301 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11] }])
    [prime_2, prime_3, prime_5, prime_11]

private theorem prime_3319 : Nat.Prime 3319 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 79] }])
    [prime_2, prime_3, prime_7, prime_79]

private theorem prime_3359 : Nat.Prime 3359 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 23, 73] }])
    [prime_2, prime_23, prime_73]

private theorem prime_3407 : Nat.Prime 3407 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 131] }])
    [prime_2, prime_13, prime_131]

private theorem prime_3527 : Nat.Prime 3527 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 41, 43] }])
    [prime_2, prime_41, prime_43]

private theorem prime_3539 : Nat.Prime 3539 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 61] }])
    [prime_2, prime_29, prime_61]

private theorem prime_3547 : Nat.Prime 3547 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 197] }])
    [prime_2, prime_3, prime_197]

private theorem prime_3637 : Nat.Prime 3637 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 101] }])
    [prime_2, prime_3, prime_101]

private theorem prime_3701 : Nat.Prime 3701 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 37] }])
    [prime_2, prime_5, prime_37]

private theorem prime_3761 : Nat.Prime 3761 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 47] }])
    [prime_2, prime_5, prime_47]

private theorem prime_3779 : Nat.Prime 3779 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1889] }])
    [prime_2, prime_1889]

private theorem prime_3793 : Nat.Prime 3793 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 79] }])
    [prime_2, prime_3, prime_79]

private theorem prime_3797 : Nat.Prime 3797 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 73] }])
    [prime_2, prime_13, prime_73]

private theorem prime_3847 : Nat.Prime 3847 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 641] }])
    [prime_2, prime_3, prime_641]

private theorem prime_3923 : Nat.Prime 3923 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 37, 53] }])
    [prime_2, prime_37, prime_53]

private theorem prime_4079 : Nat.Prime 4079 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 2039] }])
    [prime_2, prime_2039]

private theorem prime_4093 : Nat.Prime 4093 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 31] }])
    [prime_2, prime_3, prime_11, prime_31]

private theorem prime_4127 : Nat.Prime 4127 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 2063] }])
    [prime_2, prime_2063]

private theorem prime_4129 : Nat.Prime 4129 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 43] }])
    [prime_2, prime_3, prime_43]

private theorem prime_4201 : Nat.Prime 4201 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7] }])
    [prime_2, prime_3, prime_5, prime_7]

private theorem prime_4273 : Nat.Prime 4273 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 89] }])
    [prime_2, prime_3, prime_89]

private theorem prime_4363 : Nat.Prime 4363 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 727] }])
    [prime_2, prime_3, prime_727]

private theorem prime_4373 : Nat.Prime 4373 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1093] }])
    [prime_2, prime_1093]

private theorem prime_4397 : Nat.Prime 4397 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 157] }])
    [prime_2, prime_7, prime_157]

private theorem prime_4441 : Nat.Prime 4441 := by
  primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 37] }])
    [prime_2, prime_3, prime_5, prime_37]

private theorem prime_4463 : Nat.Prime 4463 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 23, 97] }])
    [prime_2, prime_23, prime_97]

private theorem prime_4513 : Nat.Prime 4513 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 47] }])
    [prime_2, prime_3, prime_47]

private theorem prime_4639 : Nat.Prime 4639 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 773] }])
    [prime_2, prime_3, prime_773]

private theorem prime_4817 : Nat.Prime 4817 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 43] }])
    [prime_2, prime_7, prime_43]

private theorem prime_4943 : Nat.Prime 4943 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 353] }])
    [prime_2, prime_7, prime_353]

private theorem prime_5051 : Nat.Prime 5051 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 101] }])
    [prime_2, prime_5, prime_101]

private theorem prime_5197 : Nat.Prime 5197 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 433] }])
    [prime_2, prime_3, prime_433]

private theorem prime_5209 : Nat.Prime 5209 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 31] }])
    [prime_2, prime_3, prime_7, prime_31]

private theorem prime_5237 : Nat.Prime 5237 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 11, 17] }])
    [prime_2, prime_7, prime_11, prime_17]

private theorem prime_5431 : Nat.Prime 5431 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 181] }])
    [prime_2, prime_3, prime_5, prime_181]

private theorem prime_5441 : Nat.Prime 5441 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17] }])
    [prime_2, prime_5, prime_17]

private theorem prime_5659 : Nat.Prime 5659 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 41] }])
    [prime_2, prime_3, prime_23, prime_41]

private theorem prime_5689 : Nat.Prime 5689 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 79] }])
    [prime_2, prime_3, prime_79]

private theorem prime_5839 : Nat.Prime 5839 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 139] }])
    [prime_2, prime_3, prime_7, prime_139]

private theorem prime_5881 : Nat.Prime 5881 := by
  primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 7] }])
    [prime_2, prime_3, prime_5, prime_7]

private theorem prime_6079 : Nat.Prime 6079 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 1013] }])
    [prime_2, prime_3, prime_1013]

private theorem prime_6173 : Nat.Prime 6173 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1543] }])
    [prime_2, prime_1543]

private theorem prime_6329 : Nat.Prime 6329 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 113] }])
    [prime_2, prime_7, prime_113]

private theorem prime_6449 : Nat.Prime 6449 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 31] }])
    [prime_2, prime_13, prime_31]

private theorem prime_6491 : Nat.Prime 6491 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 59] }])
    [prime_2, prime_5, prime_11, prime_59]

private theorem prime_6521 : Nat.Prime 6521 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 163] }])
    [prime_2, prime_5, prime_163]

private theorem prime_6553 : Nat.Prime 6553 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 13] }])
    [prime_2, prime_3, prime_7, prime_13]

private theorem prime_6577 : Nat.Prime 6577 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 137] }])
    [prime_2, prime_3, prime_137]

private theorem prime_6703 : Nat.Prime 6703 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1117] }])
    [prime_2, prime_3, prime_1117]

private theorem prime_6719 : Nat.Prime 6719 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3359] }])
    [prime_2, prime_3359]

private theorem prime_6791 : Nat.Prime 6791 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 97] }])
    [prime_2, prime_5, prime_7, prime_97]

private theorem prime_6803 : Nat.Prime 6803 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 179] }])
    [prime_2, prime_19, prime_179]

private theorem prime_6869 : Nat.Prime 6869 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 101] }])
    [prime_2, prime_17, prime_101]

private theorem prime_6917 : Nat.Prime 6917 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 19] }])
    [prime_2, prime_7, prime_13, prime_19]

private theorem prime_6949 : Nat.Prime 6949 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 193] }])
    [prime_2, prime_3, prime_193]

private theorem prime_6971 : Nat.Prime 6971 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 41] }])
    [prime_2, prime_5, prime_17, prime_41]

private theorem prime_7079 : Nat.Prime 7079 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3539] }])
    [prime_2, prime_3539]

private theorem prime_7177 : Nat.Prime 7177 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 13, 23] }])
    [prime_2, prime_3, prime_13, prime_23]

private theorem prime_7211 : Nat.Prime 7211 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 103] }])
    [prime_2, prime_5, prime_7, prime_103]

private theorem prime_7411 : Nat.Prime 7411 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 19] }])
    [prime_2, prime_3, prime_5, prime_13, prime_19]

private theorem prime_7523 : Nat.Prime 7523 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3761] }])
    [prime_2, prime_3761]

private theorem prime_7549 : Nat.Prime 7549 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 37] }])
    [prime_2, prime_3, prime_17, prime_37]

private theorem prime_7621 : Nat.Prime 7621 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 127] }])
    [prime_2, prime_3, prime_5, prime_127]

private theorem prime_7753 : Nat.Prime 7753 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 17, 19] }])
    [prime_2, prime_3, prime_17, prime_19]

private theorem prime_8171 : Nat.Prime 8171 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 43] }])
    [prime_2, prime_5, prime_19, prime_43]

private theorem prime_8269 : Nat.Prime 8269 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 53] }])
    [prime_2, prime_3, prime_13, prime_53]

private theorem prime_8329 : Nat.Prime 8329 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 347] }])
    [prime_2, prime_3, prime_347]

private theorem prime_8461 : Nat.Prime 8461 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 47] }])
    [prime_2, prime_3, prime_5, prime_47]

private theorem prime_8467 : Nat.Prime 8467 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 83] }])
    [prime_2, prime_3, prime_17, prime_83]

private theorem prime_8581 : Nat.Prime 8581 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 11, 13] }])
    [prime_2, prime_3, prime_5, prime_11, prime_13]

private theorem prime_8669 : Nat.Prime 8669 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 197] }])
    [prime_2, prime_11, prime_197]

private theorem prime_8681 : Nat.Prime 8681 := by
  primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 5, 7, 31] }])
    [prime_2, prime_5, prime_7, prime_31]

private theorem prime_8747 : Nat.Prime 8747 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 4373] }])
    [prime_2, prime_4373]

private theorem prime_8849 : Nat.Prime 8849 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 79] }])
    [prime_2, prime_7, prime_79]

private theorem prime_8893 : Nat.Prime 8893 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 19] }])
    [prime_2, prime_3, prime_13, prime_19]

private theorem prime_8971 : Nat.Prime 8971 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 23] }])
    [prime_2, prime_3, prime_5, prime_13, prime_23]

private theorem prime_9001 : Nat.Prime 9001 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5] }])
    [prime_2, prime_3, prime_5]

private theorem prime_9199 : Nat.Prime 9199 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 73] }])
    [prime_2, prime_3, prime_7, prime_73]

private theorem prime_9397 : Nat.Prime 9397 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29] }])
    [prime_2, prime_3, prime_29]

private theorem prime_9403 : Nat.Prime 9403 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1567] }])
    [prime_2, prime_3, prime_1567]

private theorem prime_9419 : Nat.Prime 9419 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 277] }])
    [prime_2, prime_17, prime_277]

private theorem prime_9613 : Nat.Prime 9613 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 89] }])
    [prime_2, prime_3, prime_89]

private theorem prime_9739 : Nat.Prime 9739 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 541] }])
    [prime_2, prime_3, prime_541]

private theorem prime_9749 : Nat.Prime 9749 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2437] }])
    [prime_2, prime_2437]

private theorem prime_9857 : Nat.Prime 9857 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11] }])
    [prime_2, prime_7, prime_11]

private theorem prime_9901 : Nat.Prime 9901 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11] }])
    [prime_2, prime_3, prime_5, prime_11]

private theorem prime_9967 : Nat.Prime 9967 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 151] }])
    [prime_2, prime_3, prime_11, prime_151]

private theorem prime_10243 : Nat.Prime 10243 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 569] }])
    [prime_2, prime_3, prime_569]

private theorem prime_10313 : Nat.Prime 10313 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1289] }])
    [prime_2, prime_1289]

private theorem prime_10453 : Nat.Prime 10453 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 67] }])
    [prime_2, prime_3, prime_13, prime_67]

private theorem prime_10459 : Nat.Prime 10459 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 83] }])
    [prime_2, prime_3, prime_7, prime_83]

private theorem prime_10739 : Nat.Prime 10739 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 13, 59] }])
    [prime_2, prime_7, prime_13, prime_59]

private theorem prime_10883 : Nat.Prime 10883 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5441] }])
    [prime_2, prime_5441]

private theorem prime_11393 : Nat.Prime 11393 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 89] }])
    [prime_2, prime_89]

private theorem prime_11701 : Nat.Prime 11701 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 13] }])
    [prime_2, prime_3, prime_5, prime_13]

private theorem prime_11777 : Nat.Prime 11777 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23] }])
    [prime_2, prime_23]

private theorem prime_11833 : Nat.Prime 11833 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 29] }])
    [prime_2, prime_3, prime_17, prime_29]

private theorem prime_11897 : Nat.Prime 11897 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1487] }])
    [prime_2, prime_1487]

private theorem prime_12503 : Nat.Prime 12503 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 19, 47] }])
    [prime_2, prime_7, prime_19, prime_47]

private theorem prime_12799 : Nat.Prime 12799 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 79] }])
    [prime_2, prime_3, prime_79]

private theorem prime_12899 : Nat.Prime 12899 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 6449] }])
    [prime_2, prime_6449]

private theorem prime_12919 : Nat.Prime 12919 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 2153] }])
    [prime_2, prime_3, prime_2153]

private theorem prime_12959 : Nat.Prime 12959 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 11, 19, 31] }])
    [prime_2, prime_11, prime_19, prime_31]

private theorem prime_13177 : Nat.Prime 13177 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 61] }])
    [prime_2, prime_3, prime_61]

private theorem prime_13309 : Nat.Prime 13309 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1109] }])
    [prime_2, prime_3, prime_1109]

private theorem prime_13751 : Nat.Prime 13751 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 11] }])
    [prime_2, prime_5, prime_11]

private theorem prime_13757 : Nat.Prime 13757 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19, 181] }])
    [prime_2, prime_19, prime_181]

private theorem prime_13807 : Nat.Prime 13807 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 59] }])
    [prime_2, prime_3, prime_13, prime_59]

private theorem prime_13873 : Nat.Prime 13873 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17] }])
    [prime_2, prime_3, prime_17]

private theorem prime_13999 : Nat.Prime 13999 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 2333] }])
    [prime_2, prime_3, prime_2333]

private theorem prime_14347 : Nat.Prime 14347 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 797] }])
    [prime_2, prime_3, prime_797]

private theorem prime_14447 : Nat.Prime 14447 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 31, 233] }])
    [prime_2, prime_31, prime_233]

private theorem prime_14747 : Nat.Prime 14747 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 73, 101] }])
    [prime_2, prime_73, prime_101]

private theorem prime_15377 : Nat.Prime 15377 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 31] }])
    [prime_2, prime_31]

private theorem prime_15581 : Nat.Prime 15581 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 41] }])
    [prime_2, prime_5, prime_19, prime_41]

private theorem prime_15641 : Nat.Prime 15641 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 17, 23] }])
    [prime_2, prime_5, prime_17, prime_23]

private theorem prime_15737 : Nat.Prime 15737 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 281] }])
    [prime_2, prime_7, prime_281]

private theorem prime_15791 : Nat.Prime 15791 := by
  primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 5, 1579] }])
    [prime_2, prime_5, prime_1579]

private theorem prime_15973 : Nat.Prime 15973 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11] }])
    [prime_2, prime_3, prime_11]

private theorem prime_16061 : Nat.Prime 16061 := by
  primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 5, 11, 73] }])
    [prime_2, prime_5, prime_11, prime_73]

private theorem prime_16253 : Nat.Prime 16253 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 239] }])
    [prime_2, prime_17, prime_239]

private theorem prime_16417 : Nat.Prime 16417 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 19] }])
    [prime_2, prime_3, prime_19]

private theorem prime_16931 : Nat.Prime 16931 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1693] }])
    [prime_2, prime_5, prime_1693]

private theorem prime_17093 : Nat.Prime 17093 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 4273] }])
    [prime_2, prime_4273]

private theorem prime_17159 : Nat.Prime 17159 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 23, 373] }])
    [prime_2, prime_23, prime_373]

private theorem prime_17467 : Nat.Prime 17467 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 71] }])
    [prime_2, prime_3, prime_41, prime_71]

private theorem prime_17669 : Nat.Prime 17669 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 631] }])
    [prime_2, prime_7, prime_631]

private theorem prime_17827 : Nat.Prime 17827 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2971] }])
    [prime_2, prime_3, prime_2971]

private theorem prime_18379 : Nat.Prime 18379 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1021] }])
    [prime_2, prime_3, prime_1021]

private theorem prime_18481 : Nat.Prime 18481 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 11] }])
    [prime_2, prime_3, prime_5, prime_7, prime_11]

private theorem prime_18583 : Nat.Prime 18583 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 163] }])
    [prime_2, prime_3, prime_19, prime_163]

private theorem prime_18637 : Nat.Prime 18637 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1553] }])
    [prime_2, prime_3, prime_1553]

private theorem prime_18701 : Nat.Prime 18701 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 17] }])
    [prime_2, prime_5, prime_11, prime_17]

private theorem prime_18839 : Nat.Prime 18839 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 9419] }])
    [prime_2, prime_9419]

private theorem prime_19403 : Nat.Prime 19403 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 89, 109] }])
    [prime_2, prime_89, prime_109]

private theorem prime_19777 : Nat.Prime 19777 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 103] }])
    [prime_2, prime_3, prime_103]

private theorem prime_19993 : Nat.Prime 19993 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 17] }])
    [prime_2, prime_3, prime_7, prime_17]

private theorem prime_20509 : Nat.Prime 20509 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1709] }])
    [prime_2, prime_3, prime_1709]

private theorem prime_21017 : Nat.Prime 21017 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 37, 71] }])
    [prime_2, prime_37, prime_71]

private theorem prime_21557 : Nat.Prime 21557 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 317] }])
    [prime_2, prime_17, prime_317]

private theorem prime_21821 : Nat.Prime 21821 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1091] }])
    [prime_2, prime_5, prime_1091]

private theorem prime_21851 : Nat.Prime 21851 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 19, 23] }])
    [prime_2, prime_5, prime_19, prime_23]

private theorem prime_22133 : Nat.Prime 22133 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 503] }])
    [prime_2, prime_11, prime_503]

private theorem prime_22159 : Nat.Prime 22159 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1231] }])
    [prime_2, prime_3, prime_1231]

private theorem prime_23539 : Nat.Prime 23539 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 3923] }])
    [prime_2, prime_3, prime_3923]

private theorem prime_24419 : Nat.Prime 24419 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 421] }])
    [prime_2, prime_29, prime_421]

private theorem prime_25693 : Nat.Prime 25693 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2141] }])
    [prime_2, prime_3, prime_2141]

private theorem prime_25799 : Nat.Prime 25799 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 12899] }])
    [prime_2, prime_12899]

private theorem prime_25919 : Nat.Prime 25919 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 12959] }])
    [prime_2, prime_12959]

private theorem prime_26309 : Nat.Prime 26309 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 6577] }])
    [prime_2, prime_6577]

private theorem prime_26437 : Nat.Prime 26437 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 2203] }])
    [prime_2, prime_3, prime_2203]

private theorem prime_27847 : Nat.Prime 27847 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 13, 17] }])
    [prime_2, prime_3, prime_7, prime_13, prime_17]

private theorem prime_28447 : Nat.Prime 28447 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 431] }])
    [prime_2, prime_3, prime_11, prime_431]

private theorem prime_29863 : Nat.Prime 29863 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 79] }])
    [prime_2, prime_3, prime_7, prime_79]

private theorem prime_30307 : Nat.Prime 30307 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5051] }])
    [prime_2, prime_3, prime_5051]

private theorem prime_31957 : Nat.Prime 31957 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2663] }])
    [prime_2, prime_3, prime_2663]

private theorem prime_32353 : Nat.Prime 32353 := by
  primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 337] }])
    [prime_2, prime_3, prime_337]

private theorem prime_33191 : Nat.Prime 33191 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 3319] }])
    [prime_2, prime_5, prime_3319]

private theorem prime_33863 : Nat.Prime 33863 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 16931] }])
    [prime_2, prime_16931]

private theorem prime_35521 : Nat.Prime 35521 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 37] }])
    [prime_2, prime_3, prime_5, prime_37]

private theorem prime_36637 : Nat.Prime 36637 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 43, 71] }])
    [prime_2, prime_3, prime_43, prime_71]

private theorem prime_36793 : Nat.Prime 36793 := by
  primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 3, 7, 73] }])
    [prime_2, prime_3, prime_7, prime_73]

private theorem prime_38671 : Nat.Prime 38671 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 1289] }])
    [prime_2, prime_3, prime_5, prime_1289]

private theorem prime_39581 : Nat.Prime 39581 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1979] }])
    [prime_2, prime_5, prime_1979]

private theorem prime_39829 : Nat.Prime 39829 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 3319] }])
    [prime_2, prime_3, prime_3319]

private theorem prime_39841 : Nat.Prime 39841 := by
  primality (cert := .witnesses [.lucas { root := 31, primeFactors := [2, 3, 5, 83] }])
    [prime_2, prime_3, prime_5, prime_83]

private theorem prime_40193 : Nat.Prime 40193 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 157] }])
    [prime_2, prime_157]

private theorem prime_41813 : Nat.Prime 41813 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 10453] }])
    [prime_2, prime_10453]

private theorem prime_41897 : Nat.Prime 41897 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5237] }])
    [prime_2, prime_5237]

private theorem prime_44383 : Nat.Prime 44383 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 569] }])
    [prime_2, prime_3, prime_13, prime_569]

private theorem prime_44953 : Nat.Prime 44953 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1873] }])
    [prime_2, prime_3, prime_1873]

private theorem prime_46633 : Nat.Prime 46633 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 29, 67] }])
    [prime_2, prime_3, prime_29, prime_67]

private theorem prime_48463 : Nat.Prime 48463 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 41, 197] }])
    [prime_2, prime_3, prime_41, prime_197]

private theorem prime_50767 : Nat.Prime 50767 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 8461] }])
    [prime_2, prime_3, prime_8461]

private theorem prime_50839 : Nat.Prime 50839 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 37, 229] }])
    [prime_2, prime_3, prime_37, prime_229]

private theorem prime_51197 : Nat.Prime 51197 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 12799] }])
    [prime_2, prime_12799]

private theorem prime_51839 : Nat.Prime 51839 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 25919] }])
    [prime_2, prime_25919]

private theorem prime_52709 : Nat.Prime 52709 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13177] }])
    [prime_2, prime_13177]

private theorem prime_53527 : Nat.Prime 53527 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 811] }])
    [prime_2, prime_3, prime_11, prime_811]

private theorem prime_59651 : Nat.Prime 59651 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1193] }])
    [prime_2, prime_5, prime_1193]

private theorem prime_59981 : Nat.Prime 59981 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 2999] }])
    [prime_2, prime_5, prime_2999]

private theorem prime_60493 : Nat.Prime 60493 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71] }])
    [prime_2, prime_3, prime_71]

private theorem prime_63487 : Nat.Prime 63487 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 3527] }])
    [prime_2, prime_3, prime_3527]

private theorem prime_67217 : Nat.Prime 67217 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 4201] }])
    [prime_2, prime_4201]

private theorem prime_68437 : Nat.Prime 68437 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1901] }])
    [prime_2, prime_3, prime_1901]

private theorem prime_69833 : Nat.Prime 69833 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 29, 43] }])
    [prime_2, prime_7, prime_29, prime_43]

private theorem prime_70381 : Nat.Prime 70381 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 17, 23] }])
    [prime_2, prime_3, prime_5, prime_17, prime_23]

private theorem prime_70451 : Nat.Prime 70451 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 1409] }])
    [prime_2, prime_5, prime_1409]

private theorem prime_72277 : Nat.Prime 72277 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 19, 317] }])
    [prime_2, prime_3, prime_19, prime_317]

private theorem prime_73517 : Nat.Prime 73517 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 18379] }])
    [prime_2, prime_18379]

private theorem prime_75821 : Nat.Prime 75821 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 223] }])
    [prime_2, prime_5, prime_17, prime_223]

private theorem prime_75941 : Nat.Prime 75941 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 3797] }])
    [prime_2, prime_5, prime_3797]

private theorem prime_76493 : Nat.Prime 76493 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 1471] }])
    [prime_2, prime_13, prime_1471]

private theorem prime_77611 : Nat.Prime 77611 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 13, 199] }])
    [prime_2, prime_3, prime_5, prime_13, prime_199]

private theorem prime_78649 : Nat.Prime 78649 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 29, 113] }])
    [prime_2, prime_3, prime_29, prime_113]

private theorem prime_79973 : Nat.Prime 79973 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 19993] }])
    [prime_2, prime_19993]

private theorem prime_80629 : Nat.Prime 80629 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 6719] }])
    [prime_2, prime_3, prime_6719]

private theorem prime_82483 : Nat.Prime 82483 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 59, 233] }])
    [prime_2, prime_3, prime_59, prime_233]

private theorem prime_83399 : Nat.Prime 83399 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 23, 37] }])
    [prime_2, prime_7, prime_23, prime_37]

private theorem prime_86183 : Nat.Prime 86183 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 41, 1051] }])
    [prime_2, prime_41, prime_1051]

private theorem prime_88843 : Nat.Prime 88843 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 17, 67] }])
    [prime_2, prime_3, prime_13, prime_17, prime_67]

private theorem prime_89189 : Nat.Prime 89189 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 2027] }])
    [prime_2, prime_11, prime_2027]

private theorem prime_94219 : Nat.Prime 94219 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 383] }])
    [prime_2, prime_3, prime_41, prime_383]

private theorem prime_97001 : Nat.Prime 97001 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 97] }])
    [prime_2, prime_5, prime_97]

private theorem prime_106921 : Nat.Prime 106921 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 5, 11] }])
    [prime_2, prime_3, prime_5, prime_11]

private theorem prime_106963 : Nat.Prime 106963 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17827] }])
    [prime_2, prime_3, prime_17827]

private theorem prime_109789 : Nat.Prime 109789 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 1307] }])
    [prime_2, prime_3, prime_7, prime_1307]

private theorem prime_111623 : Nat.Prime 111623 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 17, 67] }])
    [prime_2, prime_7, prime_17, prime_67]

private theorem prime_115597 : Nat.Prime 115597 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19] }])
    [prime_2, prime_3, prime_13, prime_19]

private theorem prime_127423 : Nat.Prime 127423 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7079] }])
    [prime_2, prime_3, prime_7079]

private theorem prime_128321 : Nat.Prime 128321 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 401] }])
    [prime_2, prime_5, prime_401]

private theorem prime_135731 : Nat.Prime 135731 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 277] }])
    [prime_2, prime_5, prime_7, prime_277]

private theorem prime_137791 : Nat.Prime 137791 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 1531] }])
    [prime_2, prime_3, prime_5, prime_1531]

private theorem prime_140639 : Nat.Prime 140639 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 19, 3701] }])
    [prime_2, prime_19, prime_3701]

private theorem prime_148301 : Nat.Prime 148301 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1483] }])
    [prime_2, prime_5, prime_1483]

private theorem prime_148513 : Nat.Prime 148513 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 13, 17] }])
    [prime_2, prime_3, prime_7, prime_13, prime_17]

private theorem prime_153533 : Nat.Prime 153533 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 131, 293] }])
    [prime_2, prime_131, prime_293]

private theorem prime_156257 : Nat.Prime 156257 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19, 257] }])
    [prime_2, prime_19, prime_257]

private theorem prime_156259 : Nat.Prime 156259 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 8681] }])
    [prime_2, prime_3, prime_8681]

private theorem prime_159473 : Nat.Prime 159473 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 9967] }])
    [prime_2, prime_9967]

private theorem prime_159671 : Nat.Prime 159671 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 2281] }])
    [prime_2, prime_5, prime_7, prime_2281]

private theorem prime_160081 : Nat.Prime 160081 := by
  primality (cert := .witnesses [.lucas { root := 28, primeFactors := [2, 3, 5, 23, 29] }])
    [prime_2, prime_3, prime_5, prime_23, prime_29]

private theorem prime_162749 : Nat.Prime 162749 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 29, 61] }])
    [prime_2, prime_23, prime_29, prime_61]

private theorem prime_163981 : Nat.Prime 163981 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 911] }])
    [prime_2, prime_3, prime_5, prime_911]

private theorem prime_166799 : Nat.Prime 166799 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 83399] }])
    [prime_2, prime_83399]

private theorem prime_170167 : Nat.Prime 170167 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 79, 359] }])
    [prime_2, prime_3, prime_79, prime_359]

private theorem prime_170189 : Nat.Prime 170189 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 157, 271] }])
    [prime_2, prime_157, prime_271]

private theorem prime_170351 : Nat.Prime 170351 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 3407] }])
    [prime_2, prime_5, prime_3407]

private theorem prime_184073 : Nat.Prime 184073 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 19, 173] }])
    [prime_2, prime_7, prime_19, prime_173]

private theorem prime_185027 : Nat.Prime 185027 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 71, 1303] }])
    [prime_2, prime_71, prime_1303]

private theorem prime_186023 : Nat.Prime 186023 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 281, 331] }])
    [prime_2, prime_281, prime_331]

private theorem prime_186211 : Nat.Prime 186211 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 2069] }])
    [prime_2, prime_3, prime_5, prime_2069]

private theorem prime_191141 : Nat.Prime 191141 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 19, 503] }])
    [prime_2, prime_5, prime_19, prime_503]

private theorem prime_194003 : Nat.Prime 194003 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 97001] }])
    [prime_2, prime_97001]

private theorem prime_194119 : Nat.Prime 194119 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 32353] }])
    [prime_2, prime_3, prime_32353]

private theorem prime_198097 : Nat.Prime 198097 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 4127] }])
    [prime_2, prime_3, prime_4127]

private theorem prime_200323 : Nat.Prime 200323 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 359] }])
    [prime_2, prime_3, prime_31, prime_359]

private theorem prime_202121 : Nat.Prime 202121 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 31, 163] }])
    [prime_2, prime_5, prime_31, prime_163]

private theorem prime_215051 : Nat.Prime 215051 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 17, 23] }])
    [prime_2, prime_5, prime_11, prime_17, prime_23]

private theorem prime_219143 : Nat.Prime 219143 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 11, 1423] }])
    [prime_2, prime_7, prime_11, prime_1423]

private theorem prime_223247 : Nat.Prime 223247 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 111623] }])
    [prime_2, prime_111623]

private theorem prime_232871 : Nat.Prime 232871 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 11, 29, 73] }])
    [prime_2, prime_5, prime_11, prime_29, prime_73]

private theorem prime_237791 : Nat.Prime 237791 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 7, 43, 79] }])
    [prime_2, prime_5, prime_7, prime_43, prime_79]

private theorem prime_243487 : Nat.Prime 243487 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 167] }])
    [prime_2, prime_3, prime_167]

private theorem prime_250619 : Nat.Prime 250619 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 29, 149] }])
    [prime_2, prime_29, prime_149]

private theorem prime_251983 : Nat.Prime 251983 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13999] }])
    [prime_2, prime_3, prime_13999]

private theorem prime_254141 : Nat.Prime 254141 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 97, 131] }])
    [prime_2, prime_5, prime_97, prime_131]

private theorem prime_261379 : Nat.Prime 261379 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 1117] }])
    [prime_2, prime_3, prime_13, prime_1117]

private theorem prime_268969 : Nat.Prime 268969 := by
  primality (cert := .witnesses [.lucas { root := 33, primeFactors := [2, 3, 7, 1601] }])
    [prime_2, prime_3, prime_7, prime_1601]

private theorem prime_269069 : Nat.Prime 269069 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 137, 491] }])
    [prime_2, prime_137, prime_491]

private theorem prime_269719 : Nat.Prime 269719 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 44953] }])
    [prime_2, prime_3, prime_44953]

private theorem prime_271463 : Nat.Prime 271463 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 135731] }])
    [prime_2, prime_135731]

private theorem prime_280639 : Nat.Prime 280639 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5197] }])
    [prime_2, prime_3, prime_5197]

private theorem prime_288109 : Nat.Prime 288109 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 53, 151] }])
    [prime_2, prime_3, prime_53, prime_151]

private theorem prime_289109 : Nat.Prime 289109 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 72277] }])
    [prime_2, prime_72277]

private theorem prime_294241 : Nat.Prime 294241 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 613] }])
    [prime_2, prime_3, prime_5, prime_613]

private theorem prime_323467 : Nat.Prime 323467 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 13, 29] }])
    [prime_2, prime_3, prime_11, prime_13, prime_29]

private theorem prime_365473 : Nat.Prime 365473 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 47] }])
    [prime_2, prime_3, prime_47]

private theorem prime_387397 : Nat.Prime 387397 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 211] }])
    [prime_2, prime_3, prime_17, prime_211]

private theorem prime_393181 : Nat.Prime 393181 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 6553] }])
    [prime_2, prime_3, prime_5, prime_6553]

private theorem prime_393413 : Nat.Prime 393413 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 59, 1667] }])
    [prime_2, prime_59, prime_1667]

private theorem prime_405959 : Nat.Prime 405959 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 107, 271] }])
    [prime_2, prime_7, prime_107, prime_271]

private theorem prime_412289 : Nat.Prime 412289 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3221] }])
    [prime_2, prime_3221]

private theorem prime_437351 : Nat.Prime 437351 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 8747] }])
    [prime_2, prime_5, prime_8747]

private theorem prime_445877 : Nat.Prime 445877 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 79, 83] }])
    [prime_2, prime_17, prime_79, prime_83]

private theorem prime_452087 : Nat.Prime 452087 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 11897] }])
    [prime_2, prime_19, prime_11897]

private theorem prime_455647 : Nat.Prime 455647 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 75941] }])
    [prime_2, prime_3, prime_75941]

private theorem prime_464383 : Nat.Prime 464383 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 25799] }])
    [prime_2, prime_3, prime_25799]

private theorem prime_465743 : Nat.Prime 465743 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 232871] }])
    [prime_2, prime_232871]

private theorem prime_474029 : Nat.Prime 474029 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 6971] }])
    [prime_2, prime_17, prime_6971]

private theorem prime_495611 : Nat.Prime 495611 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 29, 1709] }])
    [prime_2, prime_5, prime_29, prime_1709]

private theorem prime_499181 : Nat.Prime 499181 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 2269] }])
    [prime_2, prime_5, prime_11, prime_2269]

private theorem prime_499439 : Nat.Prime 499439 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 29, 79, 109] }])
    [prime_2, prime_29, prime_79, prime_109]

private theorem prime_515783 : Nat.Prime 515783 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 463, 557] }])
    [prime_2, prime_463, prime_557]

private theorem prime_520193 : Nat.Prime 520193 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 127] }])
    [prime_2, prime_127]

private theorem prime_531173 : Nat.Prime 531173 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 37, 97] }])
    [prime_2, prime_37, prime_97]

private theorem prime_562409 : Nat.Prime 562409 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 11, 83] }])
    [prime_2, prime_7, prime_11, prime_83]

private theorem prime_581029 : Nat.Prime 581029 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 6917] }])
    [prime_2, prime_3, prime_7, prime_6917]

private theorem prime_603319 : Nat.Prime 603319 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 193, 521] }])
    [prime_2, prime_3, prime_193, prime_521]

private theorem prime_657469 : Nat.Prime 657469 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 2609] }])
    [prime_2, prime_3, prime_7, prime_2609]

private theorem prime_662083 : Nat.Prime 662083 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 17, 6491] }])
    [prime_2, prime_3, prime_17, prime_6491]

private theorem prime_664529 : Nat.Prime 664529 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 41, 1013] }])
    [prime_2, prime_41, prime_1013]

private theorem prime_696079 : Nat.Prime 696079 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 38671] }])
    [prime_2, prime_3, prime_38671]

private theorem prime_725303 : Nat.Prime 725303 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 139, 2609] }])
    [prime_2, prime_139, prime_2609]

private theorem prime_735751 : Nat.Prime 735751 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 109] }])
    [prime_2, prime_3, prime_5, prime_109]

private theorem prime_820361 : Nat.Prime 820361 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 20509] }])
    [prime_2, prime_5, prime_20509]

private theorem prime_867263 : Nat.Prime 867263 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 79, 499] }])
    [prime_2, prime_11, prime_79, prime_499]

private theorem prime_941561 : Nat.Prime 941561 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 23539] }])
    [prime_2, prime_5, prime_23539]

private theorem prime_1004221 : Nat.Prime 1004221 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 797] }])
    [prime_2, prime_3, prime_5, prime_7, prime_797]

private theorem prime_1016137 : Nat.Prime 1016137 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 1283] }])
    [prime_2, prime_3, prime_11, prime_1283]

private theorem prime_1044619 : Nat.Prime 1044619 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 151, 1153] }])
    [prime_2, prime_3, prime_151, prime_1153]

private theorem prime_1197067 : Nat.Prime 1197067 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 103, 149] }])
    [prime_2, prime_3, prime_13, prime_103, prime_149]

private theorem prime_1225871 : Nat.Prime 1225871 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 5, 17, 7211] }])
    [prime_2, prime_5, prime_17, prime_7211]

private theorem prime_1232983 : Nat.Prime 1232983 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 43, 59] }])
    [prime_2, prime_3, prime_43, prime_59]

private theorem prime_1277369 : Nat.Prime 1277369 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 159671] }])
    [prime_2, prime_159671]

private theorem prime_1299439 : Nat.Prime 1299439 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 10313] }])
    [prime_2, prime_3, prime_7, prime_10313]

private theorem prime_1331123 : Nat.Prime 1331123 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 13, 51197] }])
    [prime_2, prime_13, prime_51197]

private theorem prime_1397117 : Nat.Prime 1397117 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 41, 1217] }])
    [prime_2, prime_7, prime_41, prime_1217]

private theorem prime_1416299 : Nat.Prime 1416299 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 19, 47, 61] }])
    [prime_2, prime_13, prime_19, prime_47, prime_61]

private theorem prime_1436909 : Nat.Prime 1436909 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 17, 113] }])
    [prime_2, prime_11, prime_17, prime_113]

private theorem prime_1464289 : Nat.Prime 1464289 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 7, 2179] }])
    [prime_2, prime_3, prime_7, prime_2179]

private theorem prime_1516421 : Nat.Prime 1516421 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 75821] }])
    [prime_2, prime_5, prime_75821]

private theorem prime_1598767 : Nat.Prime 1598767 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 13, 103, 199] }])
    [prime_2, prime_3, prime_13, prime_103, prime_199]

private theorem prime_1626329 : Nat.Prime 1626329 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 18481] }])
    [prime_2, prime_11, prime_18481]

private theorem prime_1643791 : Nat.Prime 1643791 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 157, 349] }])
    [prime_2, prime_3, prime_5, prime_157, prime_349]

private theorem prime_1646959 : Nat.Prime 1646959 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 19, 14447] }])
    [prime_2, prime_3, prime_19, prime_14447]

private theorem prime_1709501 : Nat.Prime 1709501 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 263] }])
    [prime_2, prime_5, prime_13, prime_263]

private theorem prime_1733383 : Nat.Prime 1733383 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 13757] }])
    [prime_2, prime_3, prime_7, prime_13757]

private theorem prime_1809887 : Nat.Prime 1809887 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 13, 151, 461] }])
    [prime_2, prime_13, prime_151, prime_461]

private theorem prime_1955123 : Nat.Prime 1955123 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 29, 2593] }])
    [prime_2, prime_13, prime_29, prime_2593]

private theorem prime_2223581 : Nat.Prime 2223581 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 73, 1523] }])
    [prime_2, prime_5, prime_73, prime_1523]

private theorem prime_2284423 : Nat.Prime 2284423 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 109, 499] }])
    [prime_2, prime_3, prime_7, prime_109, prime_499]

private theorem prime_2484931 : Nat.Prime 2484931 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 11833] }])
    [prime_2, prime_3, prime_5, prime_7, prime_11833]

private theorem prime_2500363 : Nat.Prime 2500363 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 2437] }])
    [prime_2, prime_3, prime_19, prime_2437]

private theorem prime_2629877 : Nat.Prime 2629877 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 657469] }])
    [prime_2, prime_657469]

private theorem prime_2689691 : Nat.Prime 2689691 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 268969] }])
    [prime_2, prime_5, prime_268969]

private theorem prime_2691641 : Nat.Prime 2691641 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 9613] }])
    [prime_2, prime_5, prime_7, prime_9613]

private theorem prime_2692061 : Nat.Prime 2692061 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 41, 67] }])
    [prime_2, prime_5, prime_7, prime_41, prime_67]

private theorem prime_2727173 : Nat.Prime 2727173 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 173, 563] }])
    [prime_2, prime_7, prime_173, prime_563]

private theorem prime_3264743 : Nat.Prime 3264743 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 743] }])
    [prime_2, prime_13, prime_743]

private theorem prime_3327377 : Nat.Prime 3327377 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 17, 941] }])
    [prime_2, prime_13, prime_17, prime_941]

private theorem prime_3432437 : Nat.Prime 3432437 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 7211] }])
    [prime_2, prime_7, prime_17, prime_7211]

private theorem prime_3457309 : Nat.Prime 3457309 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 288109] }])
    [prime_2, prime_3, prime_288109]

private theorem prime_3681787 : Nat.Prime 3681787 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 173, 3547] }])
    [prime_2, prime_3, prime_173, prime_3547]

private theorem prime_3995449 : Nat.Prime 3995449 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 277, 601] }])
    [prime_2, prime_3, prime_277, prime_601]

private theorem prime_4378753 : Nat.Prime 4378753 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 181] }])
    [prime_2, prime_3, prime_7, prime_181]

private theorem prime_4488961 : Nat.Prime 4488961 := by
  primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 5, 7, 167] }])
    [prime_2, prime_3, prime_5, prime_7, prime_167]

private theorem prime_4499273 : Nat.Prime 4499273 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 562409] }])
    [prime_2, prime_562409]

private theorem prime_4780729 : Nat.Prime 4780729 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 22133] }])
    [prime_2, prime_3, prime_22133]

private theorem prime_4837793 : Nat.Prime 4837793 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 8893] }])
    [prime_2, prime_17, prime_8893]

private theorem prime_4843243 : Nat.Prime 4843243 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 269069] }])
    [prime_2, prime_3, prime_269069]

private theorem prime_5343347 : Nat.Prime 5343347 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 86183] }])
    [prime_2, prime_31, prime_86183]

private theorem prime_5379383 : Nat.Prime 5379383 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 2689691] }])
    [prime_2, prime_2689691]

private theorem prime_5505713 : Nat.Prime 5505713 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 101, 3407] }])
    [prime_2, prime_101, prime_3407]

private theorem prime_6529487 : Nat.Prime 6529487 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3264743] }])
    [prime_2, prime_3264743]

private theorem prime_6579421 : Nat.Prime 6579421 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 53, 2069] }])
    [prime_2, prime_3, prime_5, prime_53, prime_2069]

private theorem prime_6829283 : Nat.Prime 6829283 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 199, 17159] }])
    [prime_2, prime_199, prime_17159]

private theorem prime_6831599 : Nat.Prime 6831599 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 23, 148513] }])
    [prime_2, prime_23, prime_148513]

private theorem prime_7588891 : Nat.Prime 7588891 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 347] }])
    [prime_2, prime_3, prime_5, prime_347]

private theorem prime_8433899 : Nat.Prime 8433899 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 11, 523, 733] }])
    [prime_2, prime_11, prime_523, prime_733]

private theorem prime_9204007 : Nat.Prime 9204007 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 219143] }])
    [prime_2, prime_3, prime_7, prime_219143]

private theorem prime_9682973 : Nat.Prime 9682973 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 186211] }])
    [prime_2, prime_13, prime_186211]

private theorem prime_9806969 : Nat.Prime 9806969 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1225871] }])
    [prime_2, prime_1225871]

private theorem prime_10257761 : Nat.Prime 10257761 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 61, 1051] }])
    [prime_2, prime_5, prime_61, prime_1051]

private theorem prime_10687669 : Nat.Prime 10687669 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 109, 8171] }])
    [prime_2, prime_3, prime_109, prime_8171]

private theorem prime_10967903 : Nat.Prime 10967903 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 19, 1381] }])
    [prime_2, prime_11, prime_19, prime_1381]

private theorem prime_11140021 : Nat.Prime 11140021 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 199, 311] }])
    [prime_2, prime_3, prime_5, prime_199, prime_311]

private theorem prime_11225507 : Nat.Prime 11225507 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 53, 137, 773] }])
    [prime_2, prime_53, prime_137, prime_773]

private theorem prime_12350017 : Nat.Prime 12350017 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 1021] }])
    [prime_2, prime_3, prime_7, prime_1021]

private theorem prime_13644847 : Nat.Prime 13644847 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 43, 61] }])
    [prime_2, prime_3, prime_17, prime_43, prime_61]

private theorem prime_13800737 : Nat.Prime 13800737 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 23, 1103] }])
    [prime_2, prime_17, prime_23, prime_1103]

private theorem prime_14367653 : Nat.Prime 14367653 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 17, 16253] }])
    [prime_2, prime_13, prime_17, prime_16253]

private theorem prime_14775301 : Nat.Prime 14775301 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 16417] }])
    [prime_2, prime_3, prime_5, prime_16417]

private theorem prime_15495881 : Nat.Prime 15495881 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 387397] }])
    [prime_2, prime_5, prime_387397]

private theorem prime_16201673 : Nat.Prime 16201673 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 67, 167, 181] }])
    [prime_2, prime_67, prime_167, prime_181]

private theorem prime_16224521 : Nat.Prime 16224521 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 41, 761] }])
    [prime_2, prime_5, prime_13, prime_41, prime_761]

private theorem prime_16453537 : Nat.Prime 16453537 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 15581] }])
    [prime_2, prime_3, prime_11, prime_15581]

private theorem prime_18013103 : Nat.Prime 18013103 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 19, 474029] }])
    [prime_2, prime_19, prime_474029]

private theorem prime_18932999 : Nat.Prime 18932999 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 29, 46633] }])
    [prime_2, prime_7, prime_29, prime_46633]

private theorem prime_20128193 : Nat.Prime 20128193 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 179, 251] }])
    [prime_2, prime_7, prime_179, prime_251]

private theorem prime_21066323 : Nat.Prime 21066323 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2777, 3793] }])
    [prime_2, prime_2777, prime_3793]

private theorem prime_22428157 : Nat.Prime 22428157 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1153, 1621] }])
    [prime_2, prime_3, prime_1153, prime_1621]

private theorem prime_23573677 : Nat.Prime 23573677 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 280639] }])
    [prime_2, prime_3, prime_7, prime_280639]

private theorem prime_23919029 : Nat.Prime 23919029 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 131, 6521] }])
    [prime_2, prime_7, prime_131, prime_6521]

private theorem prime_28276319 : Nat.Prime 28276319 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 7, 71, 28447] }])
    [prime_2, prime_7, prime_71, prime_28447]

private theorem prime_30485513 : Nat.Prime 30485513 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 277, 13757] }])
    [prime_2, prime_277, prime_13757]

private theorem prime_38339909 : Nat.Prime 38339909 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1117, 8581] }])
    [prime_2, prime_1117, prime_8581]

private theorem prime_44718253 : Nat.Prime 44718253 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 271, 13751] }])
    [prime_2, prime_3, prime_271, prime_13751]

private theorem prime_47716873 : Nat.Prime 47716873 := by
  primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 7, 431, 659] }])
    [prime_2, prime_3, prime_7, prime_431, prime_659]

private theorem prime_54459739 : Nat.Prime 54459739 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 17, 19, 29] }])
    [prime_2, prime_3, prime_17, prime_19, prime_29]

private theorem prime_55054301 : Nat.Prime 55054301 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 78649] }])
    [prime_2, prime_5, prime_7, prime_78649]

private theorem prime_56320967 : Nat.Prime 56320967 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 17, 127423] }])
    [prime_2, prime_13, prime_17, prime_127423]

private theorem prime_57619217 : Nat.Prime 57619217 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 569, 6329] }])
    [prime_2, prime_569, prime_6329]

private theorem prime_59785493 : Nat.Prime 59785493 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 353, 3257] }])
    [prime_2, prime_13, prime_353, prime_3257]

private theorem prime_60543121 : Nat.Prime 60543121 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 11, 17, 19, 71] }])
    [prime_2, prime_3, prime_5, prime_11, prime_17, prime_19, prime_71]

private theorem prime_61002247 : Nat.Prime 61002247 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 131, 77611] }])
    [prime_2, prime_3, prime_131, prime_77611]

private theorem prime_65155933 : Nat.Prime 65155933 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1809887] }])
    [prime_2, prime_3, prime_1809887]

private theorem prime_68190751 : Nat.Prime 68190751 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 30307] }])
    [prime_2, prime_3, prime_5, prime_30307]

private theorem prime_68695909 : Nat.Prime 68695909 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 71, 80629] }])
    [prime_2, prime_3, prime_71, prime_80629]

private theorem prime_70510361 : Nat.Prime 70510361 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 181, 9739] }])
    [prime_2, prime_5, prime_181, prime_9739]

private theorem prime_73872587 : Nat.Prime 73872587 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 61, 107, 5659] }])
    [prime_2, prime_61, prime_107, prime_5659]

private theorem prime_75324881 : Nat.Prime 75324881 := by
  primality (cert := .witnesses [.lucas { root := 15, primeFactors := [2, 5, 941561] }])
    [prime_2, prime_5, prime_941561]

private theorem prime_76575151 : Nat.Prime 76575151 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 170167] }])
    [prime_2, prime_3, prime_5, prime_170167]

private theorem prime_82882991 : Nat.Prime 82882991 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 5, 17, 53, 9199] }])
    [prime_2, prime_5, prime_17, prime_53, prime_9199]

private theorem prime_91066693 : Nat.Prime 91066693 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7588891] }])
    [prime_2, prime_3, prime_7588891]

private theorem prime_98406983 : Nat.Prime 98406983 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 17, 79, 36637] }])
    [prime_2, prime_17, prime_79, prime_36637]

private theorem prime_134169377 : Nat.Prime 134169377 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 67, 5689] }])
    [prime_2, prime_11, prime_67, prime_5689]

private theorem prime_181091993 : Nat.Prime 181091993 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 113, 200323] }])
    [prime_2, prime_113, prime_200323]

private theorem prime_194046283 : Nat.Prime 194046283 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 293, 36793] }])
    [prime_2, prime_3, prime_293, prime_36793]

private theorem prime_194138897 : Nat.Prime 194138897 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 1733383] }])
    [prime_2, prime_7, prime_1733383]

private theorem prime_203784211 : Nat.Prime 203784211 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 323467] }])
    [prime_2, prime_3, prime_5, prime_7, prime_323467]

private theorem prime_204878491 : Nat.Prime 204878491 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 6829283] }])
    [prime_2, prime_3, prime_5, prime_6829283]

private theorem prime_216530773 : Nat.Prime 216530773 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 97, 186023] }])
    [prime_2, prime_3, prime_97, prime_186023]

private theorem prime_224555879 : Nat.Prime 224555879 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 31, 137, 26437] }])
    [prime_2, prime_31, prime_137, prime_26437]

private theorem prime_237724499 : Nat.Prime 237724499 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 17, 563, 1129] }])
    [prime_2, prime_11, prime_17, prime_563, prime_1129]

private theorem prime_239096777 : Nat.Prime 239096777 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 23, 1299439] }])
    [prime_2, prime_23, prime_1299439]

private theorem prime_277471069 : Nat.Prime 277471069 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 7, 79, 41813] }])
    [prime_2, prime_3, prime_7, prime_79, prime_41813]

private theorem prime_282068503 : Nat.Prime 282068503 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 317, 148301] }])
    [prime_2, prime_3, prime_317, prime_148301]

private theorem prime_300089813 : Nat.Prime 300089813 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 59, 115597] }])
    [prime_2, prime_11, prime_59, prime_115597]

private theorem prime_305290673 : Nat.Prime 305290673 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 73, 261379] }])
    [prime_2, prime_73, prime_261379]

private theorem prime_332489809 : Nat.Prime 332489809 := by
  primality (cert := .witnesses [.lucas { root := 23, primeFactors := [2, 3, 7, 17, 19403] }])
    [prime_2, prime_3, prime_7, prime_17, prime_19403]

private theorem prime_337925803 : Nat.Prime 337925803 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 56320967] }])
    [prime_2, prime_3, prime_56320967]

private theorem prime_443235523 : Nat.Prime 443235523 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 73872587] }])
    [prime_2, prime_3, prime_73872587]

private theorem prime_465908257 : Nat.Prime 465908257 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 17, 41, 211] }])
    [prime_2, prime_3, prime_11, prime_17, prime_41, prime_211]

private theorem prime_545033161 : Nat.Prime 545033161 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 7, 313, 691] }])
    [prime_2, prime_3, prime_5, prime_7, prime_313, prime_691]

private theorem prime_548001149 : Nat.Prime 548001149 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 167, 820361] }])
    [prime_2, prime_167, prime_820361]

private theorem prime_603845791 : Nat.Prime 603845791 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 20128193] }])
    [prime_2, prime_3, prime_5, prime_20128193]

private theorem prime_613570187 : Nat.Prime 613570187 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 37, 139, 59651] }])
    [prime_2, prime_37, prime_139, prime_59651]

private theorem prime_624004681 : Nat.Prime 624004681 := by
  primality (cert := .witnesses [.lucas { root := 21, primeFactors := [2, 3, 5, 13, 269, 1487] }])
    [prime_2, prime_3, prime_5, prime_13, prime_269, prime_1487]

private theorem prime_660660421 : Nat.Prime 660660421 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7, 229, 6869] }])
    [prime_2, prime_3, prime_5, prime_7, prime_229, prime_6869]

private theorem prime_699539531 : Nat.Prime 699539531 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 19, 3681787] }])
    [prime_2, prime_5, prime_19, prime_3681787]

private theorem prime_720043711 : Nat.Prime 720043711 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 463, 51839] }])
    [prime_2, prime_3, prime_5, prime_463, prime_51839]

private theorem prime_741001021 : Nat.Prime 741001021 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 12350017] }])
    [prime_2, prime_3, prime_5, prime_12350017]

private theorem prime_745552679 : Nat.Prime 745552679 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 13, 419, 68437] }])
    [prime_2, prime_13, prime_419, prime_68437]

private theorem prime_784038791 : Nat.Prime 784038791 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 733, 106963] }])
    [prime_2, prime_5, prime_733, prime_106963]

private theorem prime_824629019 : Nat.Prime 824629019 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 79, 131, 39841] }])
    [prime_2, prime_79, prime_131, prime_39841]

private theorem prime_1035032137 : Nat.Prime 1035032137 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 719, 59981] }])
    [prime_2, prime_3, prime_719, prime_59981]

private theorem prime_1074261731 : Nat.Prime 1074261731 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 6803, 15791] }])
    [prime_2, prime_5, prime_6803, prime_15791]

private theorem prime_1149279811 : Nat.Prime 1149279811 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 67, 1667] }])
    [prime_2, prime_3, prime_5, prime_7, prime_67, prime_1667]

private theorem prime_1289427511 : Nat.Prime 1289427511 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 7, 281, 21851] }])
    [prime_2, prime_3, prime_5, prime_7, prime_281, prime_21851]

private theorem prime_1467855509 : Nat.Prime 1467855509 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 4817, 10883] }])
    [prime_2, prime_7, prime_4817, prime_10883]

private theorem prime_1491105359 : Nat.Prime 1491105359 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 745552679] }])
    [prime_2, prime_745552679]

private theorem prime_1589469047 : Nat.Prime 1589469047 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 53, 251, 5431] }])
    [prime_2, prime_11, prime_53, prime_251, prime_5431]

private theorem prime_1720851173 : Nat.Prime 1720851173 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 191, 383, 5881] }])
    [prime_2, prime_191, prime_383, prime_5881]

private theorem prime_2300394541 : Nat.Prime 2300394541 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 38339909] }])
    [prime_2, prime_3, prime_5, prime_38339909]

private theorem prime_3155068051 : Nat.Prime 3155068051 := by
  primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 3, 5, 29, 725303] }])
    [prime_2, prime_3, prime_5, prime_29, prime_725303]

private theorem prime_3261521227 : Nat.Prime 3261521227 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 1193, 455647] }])
    [prime_2, prime_3, prime_1193, prime_455647]

private theorem prime_3278055857 : Nat.Prime 3278055857 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 204878491] }])
    [prime_2, prime_204878491]

private theorem prime_3393158281 : Nat.Prime 3393158281 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 28276319] }])
    [prime_2, prime_3, prime_5, prime_28276319]

private theorem prime_3811955011 : Nat.Prime 3811955011 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 313, 405959] }])
    [prime_2, prime_3, prime_5, prime_313, prime_405959]

private theorem prime_4229352563 : Nat.Prime 4229352563 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 37, 2484931] }])
    [prime_2, prime_23, prime_37, prime_2484931]

private theorem prime_4381789039 : Nat.Prime 4381789039 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 47, 313, 4513] }])
    [prime_2, prime_3, prime_11, prime_47, prime_313, prime_4513]

private theorem prime_5596316249 : Nat.Prime 5596316249 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 699539531] }])
    [prime_2, prime_699539531]

private theorem prime_6434746103 : Nat.Prime 6434746103 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 89, 3847, 9397] }])
    [prime_2, prime_89, prime_3847, prime_9397]

private theorem prime_6653988127 : Nat.Prime 6653988127 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 8329, 44383] }])
    [prime_2, prime_3, prime_8329, prime_44383]

private theorem prime_6686958737 : Nat.Prime 6686958737 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 29, 227, 63487] }])
    [prime_2, prime_29, prime_227, prime_63487]

private theorem prime_7898475971 : Nat.Prime 7898475971 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 11, 10257761] }])
    [prime_2, prime_5, prime_7, prime_11, prime_10257761]

private theorem prime_8458705127 : Nat.Prime 8458705127 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 4229352563] }])
    [prime_2, prime_4229352563]

private theorem prime_9536814283 : Nat.Prime 9536814283 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1589469047] }])
    [prime_2, prime_3, prime_1589469047]

private theorem prime_10137774091 : Nat.Prime 10137774091 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 337925803] }])
    [prime_2, prime_3, prime_5, prime_337925803]

private theorem prime_11189841521 : Nat.Prime 11189841521 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 11, 13, 67, 1123] }])
    [prime_2, prime_5, prime_11, prime_13, prime_67, prime_1123]

private theorem prime_11807458601 : Nat.Prime 11807458601 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 8433899] }])
    [prime_2, prime_5, prime_7, prime_8433899]

private theorem prime_12560989307 : Nat.Prime 12560989307 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 109, 57619217] }])
    [prime_2, prime_109, prime_57619217]

private theorem prime_12616867979 : Nat.Prime 12616867979 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 13, 107, 412289] }])
    [prime_2, prime_11, prime_13, prime_107, prime_412289]

private theorem prime_13415090401 : Nat.Prime 13415090401 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 23, 9001] }])
    [prime_2, prime_3, prime_5, prime_23, prime_9001]

private theorem prime_15860556077 : Nat.Prime 15860556077 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 61, 241, 269719] }])
    [prime_2, prime_61, prime_241, prime_269719]

private theorem prime_16595578049 : Nat.Prime 16595578049 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 29, 1277369] }])
    [prime_2, prime_7, prime_29, prime_1277369]

private theorem prime_16698773461 : Nat.Prime 16698773461 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 479, 581029] }])
    [prime_2, prime_3, prime_5, prime_479, prime_581029]

private theorem prime_17404393339 : Nat.Prime 17404393339 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19, 83, 487, 1259] }])
    [prime_2, prime_3, prime_19, prime_83, prime_487, prime_1259]

private theorem prime_18365213563 : Nat.Prime 18365213563 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 569, 5379383] }])
    [prime_2, prime_3, prime_569, prime_5379383]

private theorem prime_18894140737 : Nat.Prime 18894140737 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 98406983] }])
    [prime_2, prime_3, prime_98406983]

private theorem prime_23934090899 : Nat.Prime 23934090899 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11777, 1016137] }])
    [prime_2, prime_11777, prime_1016137]

private theorem prime_24309835801 : Nat.Prime 24309835801 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 29, 1397117] }])
    [prime_2, prime_3, prime_5, prime_29, prime_1397117]

private theorem prime_25233735959 : Nat.Prime 25233735959 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 12616867979] }])
    [prime_2, prime_12616867979]

private theorem prime_25617700013 : Nat.Prime 25617700013 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 1171, 237791] }])
    [prime_2, prime_23, prime_1171, prime_237791]

private theorem prime_29259103193 : Nat.Prime 29259103193 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 332489809] }])
    [prime_2, prime_11, prime_332489809]

private theorem prime_32269652563 : Nat.Prime 32269652563 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 211, 520193] }])
    [prime_2, prime_3, prime_7, prime_211, prime_520193]

private theorem prime_45521227639 : Nat.Prime 45521227639 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 31, 107, 254141] }])
    [prime_2, prime_3, prime_31, prime_107, prime_254141]

private theorem prime_51261379201 : Nat.Prime 51261379201 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 157, 3779] }])
    [prime_2, prime_3, prime_5, prime_157, prime_3779]

private theorem prime_55234508311 : Nat.Prime 55234508311 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 68190751] }])
    [prime_2, prime_3, prime_5, prime_68190751]

private theorem prime_61913625577 : Nat.Prime 61913625577 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 131, 162749] }])
    [prime_2, prime_3, prime_11, prime_131, prime_162749]

private theorem prime_64869532121 : Nat.Prime 64869532121 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 23, 70510361] }])
    [prime_2, prime_5, prime_23, prime_70510361]

private theorem prime_69617573357 : Nat.Prime 69617573357 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17404393339] }])
    [prime_2, prime_17404393339]

private theorem prime_78546108227 : Nat.Prime 78546108227 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 53, 741001021] }])
    [prime_2, prime_53, prime_741001021]

private theorem prime_84998281217 : Nat.Prime 84998281217 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 211, 239, 823] }])
    [prime_2, prime_211, prime_239, prime_823]

private theorem prime_91892805889 : Nat.Prime 91892805889 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 13, 9204007] }])
    [prime_2, prime_3, prime_13, prime_9204007]

private theorem prime_95122940201 : Nat.Prime 95122940201 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 43, 157, 70451] }])
    [prime_2, prime_5, prime_43, prime_157, prime_70451]

private theorem prime_115397717693 : Nat.Prime 115397717693 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 383, 75324881] }])
    [prime_2, prime_383, prime_75324881]

private theorem prime_118421871779 : Nat.Prime 118421871779 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 8458705127] }])
    [prime_2, prime_7, prime_8458705127]

private theorem prime_129739064243 : Nat.Prime 129739064243 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 64869532121] }])
    [prime_2, prime_64869532121]

private theorem prime_152165406377 : Nat.Prime 152165406377 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 31, 613570187] }])
    [prime_2, prime_31, prime_613570187]

private theorem prime_170903004047 : Nat.Prime 170903004047 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 53, 11701, 137791] }])
    [prime_2, prime_53, prime_11701, prime_137791]

private theorem prime_171733557353 : Nat.Prime 171733557353 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 37, 82882991] }])
    [prime_2, prime_7, prime_37, prime_82882991]

private theorem prime_178981948919 : Nat.Prime 178981948919 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 23, 29, 134169377] }])
    [prime_2, prime_23, prime_29, prime_134169377]

private theorem prime_185931249167 : Nat.Prime 185931249167 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 397, 18013103] }])
    [prime_2, prime_13, prime_397, prime_18013103]

private theorem prime_225042442921 : Nat.Prime 225042442921 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 17, 23, 1598767] }])
    [prime_2, prime_3, prime_5, prime_17, prime_23, prime_1598767]

private theorem prime_236843743559 : Nat.Prime 236843743559 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 118421871779] }])
    [prime_2, prime_118421871779]

private theorem prime_247654502309 : Nat.Prime 247654502309 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 61913625577] }])
    [prime_2, prime_61913625577]

private theorem prime_249167942857 : Nat.Prime 249167942857 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 31, 311, 17093] }])
    [prime_2, prime_3, prime_7, prime_31, prime_311, prime_17093]

private theorem prime_260939010509 : Nat.Prime 260939010509 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 19, 3163, 8971] }])
    [prime_2, prime_11, prime_19, prime_3163, prime_8971]

private theorem prime_304553110907 : Nat.Prime 304553110907 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 59, 1051, 223247] }])
    [prime_2, prime_11, prime_59, prime_1051, prime_223247]

private theorem prime_308077619867 : Nat.Prime 308077619867 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 59, 1783, 1464289] }])
    [prime_2, prime_59, prime_1783, prime_1464289]

private theorem prime_352289044361 : Nat.Prime 352289044361 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 11, 73, 10967903] }])
    [prime_2, prime_5, prime_11, prime_73, prime_10967903]

private theorem prime_444228896581 : Nat.Prime 444228896581 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 463, 2284423] }])
    [prime_2, prime_3, prime_5, prime_7, prime_463, prime_2284423]

private theorem prime_457042474253 : Nat.Prime 457042474253 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 13, 23, 1303, 41897] }])
    [prime_2, prime_7, prime_13, prime_23, prime_1303, prime_41897]

private theorem prime_528196074449 : Nat.Prime 528196074449 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 19, 151, 1643791] }])
    [prime_2, prime_7, prime_19, prime_151, prime_1643791]

private theorem prime_531745437997 : Nat.Prime 531745437997 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 173, 431, 198097] }])
    [prime_2, prime_3, prime_173, prime_431, prime_198097]

private theorem prime_819035216627 : Nat.Prime 819035216627 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 223, 1301, 128321] }])
    [prime_2, prime_11, prime_223, prime_1301, prime_128321]

private theorem prime_1052519235013 : Nat.Prime 1052519235013 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 59, 1223, 8269] }])
    [prime_2, prime_3, prime_7, prime_59, prime_1223, prime_8269]

private theorem prime_1058113081171 : Nat.Prime 1058113081171 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7753, 1516421] }])
    [prime_2, prime_3, prime_5, prime_7753, prime_1516421]

private theorem prime_1246426684117 : Nat.Prime 1246426684117 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 6703, 15495881] }])
    [prime_2, prime_3, prime_6703, prime_15495881]

private theorem prime_1329531002801 : Nat.Prime 1329531002801 := by
  primality (cert := .witnesses [.lucas { root := 12, primeFactors := [2, 5, 7, 11, 13, 211, 15737] }])
    [prime_2, prime_5, prime_7, prime_11, prime_13, prime_211, prime_15737]

private theorem prime_1409239848217 : Nat.Prime 1409239848217 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 83, 2447, 289109] }])
    [prime_2, prime_3, prime_83, prime_2447, prime_289109]

private theorem prime_1640139724969 : Nat.Prime 1640139724969 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 156257, 437351] }])
    [prime_2, prime_3, prime_156257, prime_437351]

private theorem prime_1707429044663 : Nat.Prime 1707429044663 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 11, 47, 191, 977, 8849] }])
    [prime_2, prime_11, prime_47, prime_191, prime_977, prime_8849]

private theorem prime_1791959636407 : Nat.Prime 1791959636407 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 5839, 2692061] }])
    [prime_2, prime_3, prime_19, prime_5839, prime_2692061]

private theorem prime_2390410890781 : Nat.Prime 2390410890781 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 17, 131, 1626329] }])
    [prime_2, prime_3, prime_5, prime_11, prime_17, prime_131, prime_1626329]

private theorem prime_2659062005603 : Nat.Prime 2659062005603 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1329531002801] }])
    [prime_2, prime_1329531002801]

private theorem prime_3090004400759 : Nat.Prime 3090004400759 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 11, 181, 3187, 243487] }])
    [prime_2, prime_11, prime_181, prime_3187, prime_243487]

private theorem prime_3181817631757 : Nat.Prime 3181817631757 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 499181, 531173] }])
    [prime_2, prime_3, prime_499181, prime_531173]

private theorem prime_3414858089327 : Nat.Prime 3414858089327 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1707429044663] }])
    [prime_2, prime_1707429044663]

private theorem prime_3629323124579 : Nat.Prime 3629323124579 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 179, 10137774091] }])
    [prime_2, prime_179, prime_10137774091]

private theorem prime_3808001357081 : Nat.Prime 3808001357081 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 41, 191, 359, 33863] }])
    [prime_2, prime_5, prime_41, prime_191, prime_359, prime_33863]

private theorem prime_4130436186133 : Nat.Prime 4130436186133 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 37, 300089813] }])
    [prime_2, prime_3, prime_31, prime_37, prime_300089813]

private theorem prime_4263743552699 : Nat.Prime 4263743552699 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 304553110907] }])
    [prime_2, prime_7, prime_304553110907]

private theorem prime_5102275091939 : Nat.Prime 5102275091939 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1109, 2300394541] }])
    [prime_2, prime_1109, prime_2300394541]

private theorem prime_5190110739061 : Nat.Prime 5190110739061 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 13, 6653988127] }])
    [prime_2, prime_3, prime_5, prime_13, prime_6653988127]

private theorem prime_5934490205029 : Nat.Prime 5934490205029 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 7, 11, 5209, 1232983] }])
    [prime_2, prime_3, prime_7, prime_11, prime_5209, prime_1232983]

private theorem prime_8527487105399 : Nat.Prime 8527487105399 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 4263743552699] }])
    [prime_2, prime_4263743552699]

private theorem prime_9844277580119 : Nat.Prime 9844277580119 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3301, 1491105359] }])
    [prime_2, prime_3301, prime_1491105359]

private theorem prime_11985490465327 : Nat.Prime 11985490465327 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 7, 95122940201] }])
    [prime_2, prime_3, prime_7, prime_95122940201]

private theorem prime_12727270527029 : Nat.Prime 12727270527029 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3181817631757] }])
    [prime_2, prime_3181817631757]

private theorem prime_16167887342161 : Nat.Prime 16167887342161 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 347, 194138897] }])
    [prime_2, prime_3, prime_5, prime_347, prime_194138897]

private theorem prime_16939073890237 : Nat.Prime 16939073890237 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 89, 15860556077] }])
    [prime_2, prime_3, prime_89, prime_15860556077]

private theorem prime_23638839835777 : Nat.Prime 23638839835777 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 11, 5596316249] }])
    [prime_2, prime_3, prime_11, prime_5596316249]

private theorem prime_25956655024873 : Nat.Prime 25956655024873 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 11, 13, 2273, 3327377] }])
    [prime_2, prime_3, prime_11, prime_13, prime_2273, prime_3327377]

private theorem prime_26984839187069 : Nat.Prime 26984839187069 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 2837, 4441, 76493] }])
    [prime_2, prime_7, prime_2837, prime_4441, prime_76493]

private theorem prime_34967147477117 : Nat.Prime 34967147477117 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 43, 373, 545033161] }])
    [prime_2, prime_43, prime_373, prime_545033161]

private theorem prime_35807981731069 : Nat.Prime 35807981731069 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 129739064243] }])
    [prime_2, prime_3, prime_23, prime_129739064243]

private theorem prime_38211361654481 : Nat.Prime 38211361654481 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 113, 603845791] }])
    [prime_2, prime_5, prime_7, prime_113, prime_603845791]

private theorem prime_40681754357567 : Nat.Prime 40681754357567 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 7, 1259, 11897, 194003] }])
    [prime_2, prime_7, prime_1259, prime_11897, prime_194003]

private theorem prime_62386469563237 : Nat.Prime 62386469563237 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 13, 25693, 2223581] }])
    [prime_2, prime_3, prime_7, prime_13, prime_25693, prime_2223581]

private theorem prime_72931357581977 : Nat.Prime 72931357581977 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 79, 115397717693] }])
    [prime_2, prime_79, prime_115397717693]

private theorem prime_84838242713431 : Nat.Prime 84838242713431 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 23, 577, 4397, 48463] }])
    [prime_2, prime_3, prime_5, prime_23, prime_577, prime_4397, prime_48463]

private theorem prime_178181787378407 : Nat.Prime 178181787378407 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 12727270527029] }])
    [prime_2, prime_7, prime_12727270527029]

private theorem prime_223885671016723 : Nat.Prime 223885671016723 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 11, 13, 260939010509] }])
    [prime_2, prime_3, prime_11, prime_13, prime_260939010509]

private theorem prime_268793945461051 : Nat.Prime 268793945461051 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 1791959636407] }])
    [prime_2, prime_3, prime_5, prime_1791959636407]

private theorem prime_409506045472427 : Nat.Prime 409506045472427 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 7549, 15377, 251983] }])
    [prime_2, prime_7, prime_7549, prime_15377, prime_251983]

private theorem prime_539637671397211 : Nat.Prime 539637671397211 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 17, 1058113081171] }])
    [prime_2, prime_3, prime_5, prime_17, prime_1058113081171]

private theorem prime_846072166972733 : Nat.Prime 846072166972733 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 17, 373, 22159, 215051] }])
    [prime_2, prime_7, prime_17, prime_373, prime_22159, prime_215051]

private theorem prime_1220147524386821 : Nat.Prime 1220147524386821 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 170351, 21066323] }])
    [prime_2, prime_5, prime_17, prime_170351, prime_21066323]

private theorem prime_1359908047647257 : Nat.Prime 1359908047647257 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 10243, 16595578049] }])
    [prime_2, prime_10243, prime_16595578049]

private theorem prime_1497275269517689 : Nat.Prime 1497275269517689 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 62386469563237] }])
    [prime_2, prime_3, prime_62386469563237]

private theorem prime_1710906597572093 : Nat.Prime 1710906597572093 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 53, 101, 31957, 2500363] }])
    [prime_2, prime_53, prime_101, prime_31957, prime_2500363]

private theorem prime_2120173135571167 : Nat.Prime 2120173135571167 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 13, 929, 29259103193] }])
    [prime_2, prime_3, prime_13, prime_929, prime_29259103193]

private theorem prime_2932104139776199 : Nat.Prime 2932104139776199 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5343347, 30485513] }])
    [prime_2, prime_3, prime_5343347, prime_30485513]

private theorem prime_4198838776908691 : Nat.Prime 4198838776908691 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 7621, 18365213563] }])
    [prime_2, prime_3, prime_5, prime_7621, prime_18365213563]

private theorem prime_4959332315574437 : Nat.Prime 4959332315574437 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 72931357581977] }])
    [prime_2, prime_17, prime_72931357581977]

private theorem prime_5417697128646709 : Nat.Prime 5417697128646709 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 43, 152165406377] }])
    [prime_2, prime_3, prime_23, prime_43, prime_152165406377]

private theorem prime_8545092473402167 : Nat.Prime 8545092473402167 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 11, 191, 631, 1074261731] }])
    [prime_2, prime_3, prime_11, prime_191, prime_631, prime_1074261731]

private theorem prime_11631987469251529 : Nat.Prime 11631987469251529 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 19, 73, 271, 1289427511] }])
    [prime_2, prime_3, prime_19, prime_73, prime_271, prime_1289427511]

private theorem prime_11728416559104797 : Nat.Prime 11728416559104797 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 2932104139776199] }])
    [prime_2, prime_2932104139776199]

private theorem prime_12130340098238161 : Nat.Prime 12130340098238161 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 735751, 68695909] }])
    [prime_2, prime_3, prime_5, prime_735751, prime_68695909]

private theorem prime_12165237289205323 : Nat.Prime 12165237289205323 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 17, 9901, 1720851173] }])
    [prime_2, prime_3, prime_7, prime_17, prime_9901, prime_1720851173]

private theorem prime_12337092226150547 : Nat.Prime 12337092226150547 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1955123, 3155068051] }])
    [prime_2, prime_1955123, prime_3155068051]

private theorem prime_14287215088855133 : Nat.Prime 14287215088855133 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 37, 9403, 277471069] }])
    [prime_2, prime_37, prime_9403, prime_277471069]

private theorem prime_16646149615358383 : Nat.Prime 16646149615358383 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 139, 227, 12560989307] }])
    [prime_2, prime_3, prime_7, prime_139, prime_227, prime_12560989307]

private theorem prime_18871607480183113 : Nat.Prime 18871607480183113 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 113, 881, 7898475971] }])
    [prime_2, prime_3, prime_113, prime_881, prime_7898475971]

private theorem prime_19415663027560739 : Nat.Prime 19415663027560739 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 569, 3181, 10739, 499439] }])
    [prime_2, prime_569, prime_3181, prime_10739, prime_499439]

private theorem prime_20592781911084953 : Nat.Prime 20592781911084953 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 19, 603319, 224555879] }])
    [prime_2, prime_19, prime_603319, prime_224555879]

private theorem prime_21670788514586837 : Nat.Prime 21670788514586837 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5417697128646709] }])
    [prime_2, prime_5417697128646709]

private theorem prime_24402950487736421 : Nat.Prime 24402950487736421 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 1220147524386821] }])
    [prime_2, prime_5, prime_1220147524386821]

private theorem prime_26650666205909651 : Nat.Prime 26650666205909651 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 89, 352289044361] }])
    [prime_2, prime_5, prime_17, prime_89, prime_352289044361]

private theorem prime_44368367631876037 : Nat.Prime 44368367631876037 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 101, 149, 35521, 109789] }])
    [prime_2, prime_3, prime_7, prime_101, prime_149, prime_35521, prime_109789]

private theorem prime_45160500800146357 : Nat.Prime 45160500800146357 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 313, 50767, 3432437] }])
    [prime_2, prime_3, prime_23, prime_313, prime_50767, prime_3432437]

private theorem prime_59691479354730757 : Nat.Prime 59691479354730757 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 19, 71, 19777, 4780729] }])
    [prime_2, prime_3, prime_13, prime_19, prime_71, prime_19777, prime_4780729]

private theorem prime_64824909609147439 : Nat.Prime 64824909609147439 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 421, 1913, 13415090401] }])
    [prime_2, prime_3, prime_421, prime_1913, prime_13415090401]

private theorem prime_65757420630437317 : Nat.Prime 65757420630437317 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 11, 11140021, 44718253] }])
    [prime_2, prime_3, prime_11, prime_11140021, prime_44718253]

private theorem prime_73435034572951879 : Nat.Prime 73435034572951879 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 1359908047647257] }])
    [prime_2, prime_3, prime_1359908047647257]

private theorem prime_74051137823220347 : Nat.Prime 74051137823220347 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 61, 293, 13309, 294241] }])
    [prime_2, prime_23, prime_61, prime_293, prime_13309, prime_294241]

private theorem prime_85920744243882959 : Nat.Prime 85920744243882959 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 156259, 194119, 1416299] }])
    [prime_2, prime_156259, prime_194119, prime_1416299]

private theorem prime_160005724907991899 : Nat.Prime 160005724907991899 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 17, 61, 5934490205029] }])
    [prime_2, prime_13, prime_17, prime_61, prime_5934490205029]

private theorem prime_173434993427620621 : Nat.Prime 173434993427620621 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 17, 59, 89, 53527, 67217] }])
    [prime_2, prime_3, prime_5, prime_17, prime_59, prime_89, prime_53527, prime_67217]

private theorem prime_232987956330728869 : Nat.Prime 232987956330728869 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 19415663027560739] }])
    [prime_2, prime_3, prime_19415663027560739]

private theorem prime_327586413514470491 : Nat.Prime 327586413514470491 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 17, 6831599, 282068503] }])
    [prime_2, prime_5, prime_17, prime_6831599, prime_282068503]

private theorem prime_348580593106498631 : Nat.Prime 348580593106498631 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 5, 10687669, 3261521227] }])
    [prime_2, prime_5, prime_10687669, prime_3261521227]

private theorem prime_586251408063791101 : Nat.Prime 586251408063791101 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 5, 383, 5102275091939] }])
    [prime_2, prime_3, prime_5, prime_383, prime_5102275091939]

private theorem prime_609303719034692009 : Nat.Prime 609303719034692009 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 52709, 84998281217] }])
    [prime_2, prime_17, prime_52709, prime_84998281217]

private theorem prime_672174090717627731 : Nat.Prime 672174090717627731 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 83, 1523, 531745437997] }])
    [prime_2, prime_5, prime_83, prime_1523, prime_531745437997]

private theorem prime_684750413430230317 : Nat.Prime 684750413430230317 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 41, 241, 444228896581] }])
    [prime_2, prime_3, prime_13, prime_41, prime_241, prime_444228896581]

private theorem prime_737829704623388977 : Nat.Prime 737829704623388977 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 3761, 7523, 181091993] }])
    [prime_2, prime_3, prime_3761, prime_7523, prime_181091993]

private theorem prime_1013919507334978087 : Nat.Prime 1013919507334978087 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 19, 61, 1709501, 4488961] }])
    [prime_2, prime_3, prime_19, prime_61, prime_1709501, prime_4488961]

private theorem prime_1429481932745436223 : Nat.Prime 1429481932745436223 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 1331123, 178981948919] }])
    [prime_2, prime_3, prime_1331123, prime_178981948919]

private theorem prime_2340303689068525729 : Nat.Prime 2340303689068525729 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 2239, 3629323124579] }])
    [prime_2, prime_3, prime_2239, prime_3629323124579]

private theorem prime_2907175561681101541 : Nat.Prime 2907175561681101541 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 479, 1453, 69617573357] }])
    [prime_2, prime_3, prime_5, prime_479, prime_1453, prime_69617573357]

private theorem prime_6258674133552522623 : Nat.Prime 6258674133552522623 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 73, 13873, 3090004400759] }])
    [prime_2, prime_73, prime_13873, prime_3090004400759]

private theorem prime_7127810107612771261 : Nat.Prime 7127810107612771261 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 67, 157, 696079, 16224521] }])
    [prime_2, prime_3, prime_5, prime_67, prime_157, prime_696079, prime_16224521]

private theorem prime_7391188437184512407 : Nat.Prime 7391188437184512407 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 6079, 18839, 32269652563] }])
    [prime_2, prime_6079, prime_18839, prime_32269652563]

private theorem prime_9546554494483744271 : Nat.Prime 9546554494483744271 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 5, 13, 73435034572951879] }])
    [prime_2, prime_5, prime_13, prime_73435034572951879]

private theorem prime_9902855019602828533 : Nat.Prime 9902855019602828533 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 662083, 1246426684117] }])
    [prime_2, prime_3, prime_662083, prime_1246426684117]

private theorem prime_10956006614883685073 : Nat.Prime 10956006614883685073 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 684750413430230317] }])
    [prime_2, prime_684750413430230317]

private theorem prime_20729564340805870393 : Nat.Prime 20729564340805870393 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 71, 12165237289205323] }])
    [prime_2, prime_3, prime_71, prime_12165237289205323]

private theorem prime_28990705179430868149 : Nat.Prime 28990705179430868149 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 11, 24402950487736421] }])
    [prime_2, prime_3, prime_11, prime_24402950487736421]

private theorem prime_31114725039669738547 : Nat.Prime 31114725039669738547 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 1153, 17467, 9536814283] }])
    [prime_2, prime_3, prime_1153, prime_17467, prime_9536814283]

private theorem prime_43766792433758111411 : Nat.Prime 43766792433758111411 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 11, 29, 178181787378407] }])
    [prime_2, prime_5, prime_7, prime_11, prime_29, prime_178181787378407]

private theorem prime_57402922320327635417 : Nat.Prime 57402922320327635417 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 1811, 8669, 457042474253] }])
    [prime_2, prime_1811, prime_8669, prime_457042474253]

private theorem prime_70411060116013297943 : Nat.Prime 70411060116013297943 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 1321, 26650666205909651] }])
    [prime_2, prime_1321, prime_26650666205909651]

private theorem prime_113377346766489787873 : Nat.Prime 113377346766489787873 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 137, 389, 26309, 76575151] }])
    [prime_2, prime_3, prime_11, prime_137, prime_389, prime_26309, prime_76575151]

private theorem prime_143275110596945484931 : Nat.Prime 143275110596945484931 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 107, 4959332315574437] }])
    [prime_2, prime_3, prime_5, prime_107, prime_4959332315574437]

private theorem prime_219120132297673701461 : Nat.Prime 219120132297673701461 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 10956006614883685073] }])
    [prime_2, prime_5, prime_10956006614883685073]

private theorem prime_235074455284844477681 : Nat.Prime 235074455284844477681 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 5, 7, 4079, 15641, 69833, 94219] }])
    [prime_2, prime_5, prime_7, prime_4079, prime_15641, prime_69833, prime_94219]

private theorem prime_367572856860929704339 : Nat.Prime 367572856860929704339 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 31, 107, 6173, 88843, 11225507] }])
    [prime_2, prime_3, prime_31, prime_107, prime_6173, prime_88843, prime_11225507]

private theorem prime_436439480219666491433 : Nat.Prime 436439480219666491433 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 2341, 9749, 2390410890781] }])
    [prime_2, prime_2341, prime_9749, prime_2390410890781]

private theorem prime_466572076719054600611 : Nat.Prime 466572076719054600611 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 2153, 21670788514586837] }])
    [prime_2, prime_5, prime_2153, prime_21670788514586837]

private theorem prime_696408315308133311189 : Nat.Prime 696408315308133311189 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 10459, 16646149615358383] }])
    [prime_2, prime_10459, prime_16646149615358383]

private theorem prime_790728104230020418109 : Nat.Prime 790728104230020418109 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 23, 79973, 452087, 237724499] }])
    [prime_2, prime_23, prime_79973, prime_452087, prime_237724499]

private theorem prime_796902197119382615623 : Nat.Prime 796902197119382615623 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 17, 173, 45160500800146357] }])
    [prime_2, prime_3, prime_17, prime_173, prime_45160500800146357]

private theorem prime_964205119896232600349 : Nat.Prime 964205119896232600349 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 103, 2340303689068525729] }])
    [prime_2, prime_103, prime_2340303689068525729]

private theorem prime_1324980160979227708729 : Nat.Prime 1324980160979227708729 := by
  primality (cert := .witnesses [.lucas { root := 29, primeFactors := [2, 3, 37, 4843243, 308077619867] }])
    [prime_2, prime_3, prime_37, prime_4843243, prime_308077619867]

private theorem prime_1483691410841187695993 : Nat.Prime 1483691410841187695993 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 239, 59691479354730757] }])
    [prime_2, prime_13, prime_239, prime_59691479354730757]

private theorem prime_2967382821682375391987 : Nat.Prime 2967382821682375391987 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1483691410841187695993] }])
    [prime_2, prime_1483691410841187695993]

private theorem prime_4472975565824772091513 : Nat.Prime 4472975565824772091513 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 7, 79, 823, 409506045472427] }])
    [prime_2, prime_3, prime_7, prime_79, prime_823, prime_409506045472427]

private theorem prime_4798989825055906043903 : Nat.Prime 4798989825055906043903 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 13, 12919, 14287215088855133] }])
    [prime_2, prime_13, prime_12919, prime_14287215088855133]

private theorem prime_7247126127611210431519 : Nat.Prime 7247126127611210431519 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 33191, 12130340098238161] }])
    [prime_2, prime_3, prime_33191, prime_12130340098238161]

private theorem prime_7247676294857717037251 : Nat.Prime 7247676294857717037251 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 28990705179430868149] }])
    [prime_2, prime_5, prime_28990705179430868149]

private theorem prime_8986098488526789298859 : Nat.Prime 8986098488526789298859 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 7, 2691641, 4378753, 54459739] }])
    [prime_2, prime_7, prime_2691641, prime_4378753, prime_54459739]

private theorem prime_11040728444890860856313 : Nat.Prime 11040728444890860856313 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 18637, 74051137823220347] }])
    [prime_2, prime_18637, prime_74051137823220347]

private theorem prime_16724006169635845174921 : Nat.Prime 16724006169635845174921 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 5, 7, 173, 3637, 21557, 1467855509] }])
    [prime_2, prime_3, prime_5, prime_7, prime_173, prime_3637, prime_21557, prime_1467855509]

private theorem prime_19675661775892873533193 : Nat.Prime 19675661775892873533193 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 41, 971, 20592781911084953] }])
    [prime_2, prime_3, prime_41, prime_971, prime_20592781911084953]

private theorem prime_22524139113102022376759 : Nat.Prime 22524139113102022376759 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 293, 185027, 445877, 465908257] }])
    [prime_2, prime_293, prime_185027, prime_445877, prime_465908257]

private theorem prime_37765775766444803564779 : Nat.Prime 37765775766444803564779 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 24419, 85920744243882959] }])
    [prime_2, prime_3, prime_24419, prime_85920744243882959]

private theorem prime_40721184886701170073421 : Nat.Prime 40721184886701170073421 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 11, 59, 348580593106498631] }])
    [prime_2, prime_3, prime_5, prime_11, prime_59, prime_348580593106498631]

private theorem prime_45048278226204044753519 : Nat.Prime 45048278226204044753519 := by
  primality (cert := .witnesses [.lucas { root := 19, primeFactors := [2, 22524139113102022376759] }])
    [prime_2, prime_22524139113102022376759]

private theorem prime_62549172628733163298493 : Nat.Prime 62549172628733163298493 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 24309835801, 91892805889] }])
    [prime_2, prime_7, prime_24309835801, prime_91892805889]

private theorem prime_148397778029673503377649 : Nat.Prime 148397778029673503377649 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 7, 1324980160979227708729] }])
    [prime_2, prime_7, prime_1324980160979227708729]

private theorem prime_241642156918656757437917 : Nat.Prime 241642156918656757437917 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 7, 720043711, 11985490465327] }])
    [prime_2, prime_7, prime_720043711, prime_11985490465327]

private theorem prime_293743964895886464133067 : Nat.Prime 293743964895886464133067 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 55234508311, 2659062005603] }])
    [prime_2, prime_55234508311, prime_2659062005603]

private theorem prime_689269393474878725410241 : Nat.Prime 689269393474878725410241 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 1499, 11393, 202121, 624004681] }])
    [prime_2, prime_5, prime_1499, prime_11393, prime_202121, prime_624004681]

private theorem prime_1184744750656369110401693 : Nat.Prime 1184744750656369110401693 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 73517, 23573677, 170903004047] }])
    [prime_2, prime_73517, prime_23573677, prime_170903004047]

private theorem prime_1967995580973679893030139 : Nat.Prime 1967995580973679893030139 := by
  primality (cert := .witnesses [.lucas { root := 10, primeFactors := [2, 3, 41, 107, 379, 65757420630437317] }])
    [prime_2, prime_3, prime_41, prime_107, prime_379, prime_65757420630437317]

private theorem prime_3300640663614376146281081 : Nat.Prime 3300640663614376146281081 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 79, 269, 307, 331, 38211361654481] }])
    [prime_2, prime_5, prime_79, prime_269, prime_307, prime_331, prime_38211361654481]

private theorem prime_3806163106148632912040801 : Nat.Prime 3806163106148632912040801 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 13, 73, 431, 11631987469251529] }])
    [prime_2, prime_5, prime_13, prime_73, prime_431, prime_11631987469251529]

private theorem prime_4955310604882444922887091 : Nat.Prime 4955310604882444922887091 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 45048278226204044753519] }])
    [prime_2, prime_5, prime_11, prime_45048278226204044753519]

private theorem prime_7943792115876860313934333 : Nat.Prime 7943792115876860313934333 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 163981, 170189, 184073, 2629877] }])
    [prime_2, prime_3, prime_7, prime_163981, prime_170189, prime_184073, prime_2629877]

private theorem prime_25113873750955409967111979 : Nat.Prime 25113873750955409967111979 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 7, 16698773461, 35807981731069] }])
    [prime_2, prime_3, prime_7, prime_16698773461, prime_35807981731069]

private theorem prime_31163533386231435709306291 : Nat.Prime 31163533386231435709306291 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 3, 5, 7, 148397778029673503377649] }])
    [prime_2, prime_3, prime_5, prime_7, prime_148397778029673503377649]

private theorem prime_59463727258589339074645093 : Nat.Prime 59463727258589339074645093 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 4955310604882444922887091] }])
    [prime_2, prime_3, prime_4955310604882444922887091]

private theorem prime_87773791136882343807688351 : Nat.Prime 87773791136882343807688351 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 53, 11040728444890860856313] }])
    [prime_2, prime_3, prime_5, prime_53, prime_11040728444890860856313]

private theorem prime_90111722524121135364336749 : Nat.Prime 90111722524121135364336749 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 541, 863, 70381, 14367653, 47716873] }])
    [prime_2, prime_541, prime_863, prime_70381, prime_14367653, prime_47716873]

private theorem prime_103380421590861773779384673 : Nat.Prime 103380421590861773779384673 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 4639, 696408315308133311189] }])
    [prime_2, prime_4639, prime_696408315308133311189]

private theorem prime_182695829095134379777958449 : Nat.Prime 182695829095134379777958449 := by
  primality (cert := .witnesses [.lucas { root := 14, primeFactors := [2, 3, 3806163106148632912040801] }])
    [prime_2, prime_3, prime_3806163106148632912040801]

private theorem prime_188132699053539041681898539 : Nat.Prime 188132699053539041681898539 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 9806969, 737829704623388977] }])
    [prime_2, prime_13, prime_9806969, prime_737829704623388977]

private theorem prime_430825719001614093834776837 : Nat.Prime 430825719001614093834776837 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 31, 41, 389, 9682973, 185931249167] }])
    [prime_2, prime_11, prime_31, prime_41, prime_389, prime_9682973, prime_185931249167]

private theorem prime_1304391581691663426332752597 : Nat.Prime 1304391581691663426332752597 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 29, 2857, 153533, 8545092473402167] }])
    [prime_2, prime_3, prime_29, prime_2857, prime_153533, prime_8545092473402167]

private theorem prime_3698981908496563538334808637 : Nat.Prime 3698981908496563538334808637 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 4130436186133, 223885671016723] }])
    [prime_2, prime_4130436186133, prime_223885671016723]

private theorem prime_5143144907223462196121419109 : Nat.Prime 5143144907223462196121419109 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 13, 139, 397, 1197067, 1497275269517689] }])
    [prime_2, prime_13, prime_139, prime_397, prime_1197067, prime_1497275269517689]

private theorem prime_6121906817230227457421419373 : Nat.Prime 6121906817230227457421419373 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 1607, 2591, 367572856860929704339] }])
    [prime_2, prime_1607, prime_2591, prime_367572856860929704339]

private theorem prime_9306492889034384639357270029 : Nat.Prime 9306492889034384639357270029 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 13, 71, 7411, 113377346766489787873] }])
    [prime_2, prime_3, prime_13, prime_71, prime_7411, prime_113377346766489787873]

private theorem prime_17872557694074308203773625711 : Nat.Prime 17872557694074308203773625711 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 5, 11, 29, 947, 219120132297673701461] }])
    [prime_2, prime_3, prime_5, prime_11, prime_29, prime_947, prime_219120132297673701461]

private theorem prime_22295788290028023187553755183 : Nat.Prime 22295788290028023187553755183 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 151, 193, 6791, 6258674133552522623] }])
    [prime_2, prime_3, prime_151, prime_193, prime_6791, prime_6258674133552522623]

private theorem prime_120086191132872757931474643029 : Nat.Prime 120086191132872757931474643029 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31, 79, 733, 16724006169635845174921] }])
    [prime_2, prime_31, prime_79, prime_733, prime_16724006169635845174921]

private theorem prime_310537106619460598367623638699 : Nat.Prime 310537106619460598367623638699 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 281, 21017, 464383, 18871607480183113] }])
    [prime_2, prime_3, prime_281, prime_21017, prime_464383, prime_18871607480183113]

private theorem prime_614486262938376971075295902173 : Nat.Prime 614486262938376971075295902173 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 2039, 25113873750955409967111979] }])
    [prime_2, prime_3, prime_2039, prime_25113873750955409967111979]

private theorem prime_1062087521365893764794464830219 : Nat.Prime 1062087521365893764794464830219 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 25617700013, 20729564340805870393] }])
    [prime_2, prime_25617700013, prime_20729564340805870393]

private theorem prime_1679090654706576081276965528741 : Nat.Prime 1679090654706576081276965528741 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 13, 227, 495611, 57402922320327635417] }])
    [prime_2, prime_5, prime_13, prime_227, prime_495611, prime_57402922320327635417]

private theorem prime_1880300943357093015204166625453 : Nat.Prime 1880300943357093015204166625453 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 769, 2081, 293743964895886464133067] }])
    [prime_2, prime_769, prime_2081, prime_293743964895886464133067]

private theorem prime_11281805660142558091224999752719 : Nat.Prime 11281805660142558091224999752719 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 1880300943357093015204166625453] }])
    [prime_2, prime_3, prime_1880300943357093015204166625453]

private theorem prime_23517938481625168713689529984419 : Nat.Prime 23517938481625168713689529984419 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 1783, 60543121, 9902855019602828533] }])
    [prime_2, prime_11, prime_1783, prime_60543121, prime_9902855019602828533]

private theorem prime_44424403584155672970130317933443 : Nat.Prime 44424403584155672970130317933443 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 203784211, 6434746103, 16939073890237] }])
    [prime_2, prime_203784211, prime_6434746103, prime_16939073890237]

private theorem prime_53095344600632489279481430824043 : Nat.Prime 53095344600632489279481430824043 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 824629019, 466572076719054600611] }])
    [prime_2, prime_3, prime_23, prime_824629019, prime_466572076719054600611]

private theorem prime_148185389845758273776166259068011 : Nat.Prime 148185389845758273776166259068011 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 11, 47, 163, 18894140737, 846072166972733] }])
    [prime_2, prime_5, prime_11, prime_47, prime_163, prime_18894140737, prime_846072166972733]

private theorem prime_206604670206701803811530905178951 : Nat.Prime 206604670206701803811530905178951 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 5, 137, 1621, 18932999, 327586413514470491] }])
    [prime_2, prime_3, prime_5, prime_137, prime_1621, prime_18932999, prime_327586413514470491]

private theorem prime_241434703923132836908859374841623 : Nat.Prime 241434703923132836908859374841623 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 11, 73, 227, 293, 7177, 443235523, 236843743559] }])
    [prime_2, prime_3, prime_11, prime_73, prime_227, prime_293, prime_7177, prime_443235523, prime_236843743559]

private theorem prime_258025284322543384519614454542257 : Nat.Prime 258025284322543384519614454542257 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 61002247, 37765775766444803564779] }])
    [prime_2, prime_7, prime_61002247, prime_37765775766444803564779]

private theorem prime_1312542657636373210216832047041529 : Nat.Prime 1312542657636373210216832047041529 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 89, 614486262938376971075295902173] }])
    [prime_2, prime_3, prime_89, prime_614486262938376971075295902173]

private theorem prime_1314355747271930081520716037054557 : Nat.Prime 1314355747271930081520716037054557 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 53, 337, 140639, 247654502309, 528196074449] }])
    [prime_2, prime_53, prime_337, prime_140639, prime_247654502309, prime_528196074449]

private theorem prime_2334883492874075436752948849671373 : Nat.Prime 2334883492874075436752948849671373 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 17, 3457309, 14775301, 672174090717627731] }])
    [prime_2, prime_17, prime_3457309, prime_14775301, prime_672174090717627731]

private theorem prime_2379064336227843720753580395165293 : Nat.Prime 2379064336227843720753580395165293 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 181, 859, 4837793, 790728104230020418109] }])
    [prime_2, prime_181, prime_859, prime_4837793, prime_790728104230020418109]

private theorem prime_15931220785794892918748144039803783 : Nat.Prime 15931220785794892918748144039803783 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 41, 18583, 78546108227, 44368367631876037] }])
    [prime_2, prime_3, prime_41, prime_18583, prime_78546108227, prime_44368367631876037]

private theorem prime_18968965517771824668852161885522759 : Nat.Prime 18968965517771824668852161885522759 := by
  primality (cert := .witnesses [.lucas { root := 17, primeFactors := [2, 13644847, 239096777, 2907175561681101541] }])
    [prime_2, prime_13644847, prime_239096777, prime_2907175561681101541]

private theorem prime_285944334375598337130734239460815999 : Nat.Prime 285944334375598337130734239460815999 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 3, 47, 22428157, 194046283, 232987956330728869] }])
    [prime_2, prime_3, prime_47, prime_22428157, prime_194046283, prime_232987956330728869]

private theorem prime_2503903448345880856288485368889004189 : Nat.Prime 2503903448345880856288485368889004189 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 3, 11, 18968965517771824668852161885522759] }])
    [prime_2, prime_3, prime_11, prime_18968965517771824668852161885522759]

private theorem prime_21822669621025437945920900307909707927 : Nat.Prime 21822669621025437945920900307909707927 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 7, 67, 157, 148185389845758273776166259068011] }])
    [prime_2, prime_7, prime_67, prime_157, prime_148185389845758273776166259068011]

private theorem prime_34666336429889686991195961430613031809 : Nat.Prime 34666336429889686991195961430613031809 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 17, 15931220785794892918748144039803783] }])
    [prime_2, prime_17, prime_15931220785794892918748144039803783]

private theorem prime_251388255843157574082560649419464520147 : Nat.Prime 251388255843157574082560649419464520147 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 13, 41, 137, 3995449, 430825719001614093834776837] }])
    [prime_2, prime_13, prime_41, prime_137, prime_3995449, prime_430825719001614093834776837]

private theorem prime_493135792716147357863898385429374055811 : Nat.Prime 493135792716147357863898385429374055811 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 7, 13, 1801, 1646959, 182695829095134379777958449] }])
    [prime_2, prime_5, prime_7, prime_13, prime_1801, prime_1646959, prime_182695829095134379777958449]

private theorem prime_736284508682742314451747640390872415321 : Nat.Prime 736284508682742314451747640390872415321 := by
  primality (cert := .witnesses [.lucas { root := 7, primeFactors := [2, 3, 5, 39581, 191141, 90111722524121135364336749] }])
    [prime_2, prime_3, prime_5, prime_39581, prime_191141, prime_90111722524121135364336749]

private theorem prime_112212283125426861484157226343289292343609 : Nat.Prime 112212283125426861484157226343289292343609 := by
  primality (cert := .witnesses [.lucas { root := 11, primeFactors := [2, 3, 173434993427620621, 8986098488526789298859] }])
    [prime_2, prime_3, prime_173434993427620621, prime_8986098488526789298859]

private theorem prime_238161085274207532887920315503093489421271 : Nat.Prime 238161085274207532887920315503093489421271 := by
  primality (cert := .witnesses [.lucas { root := 13, primeFactors := [2, 5, 7, 29, 250619, 271463, 59463727258589339074645093] }])
    [prime_2, prime_5, prime_7, prime_29, prime_250619, prime_271463, prime_59463727258589339074645093]

private theorem prime_2488427089502770379620570664240050424389777 : Nat.Prime 2488427089502770379620570664240050424389777 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 660660421, 2120173135571167, 12337092226150547] }])
    [prime_2, prime_3, prime_660660421, prime_2120173135571167, prime_12337092226150547]

private theorem prime_472992154780007014687741096600552489796295397 : Nat.Prime 472992154780007014687741096600552489796295397 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 349, 4943, 18701, 8527487105399, 143275110596945484931] }])
    [prime_2, prime_3, prime_349, prime_4943, prime_18701, prime_8527487105399, prime_143275110596945484931]

private theorem prime_4353861596170690667575550484357142297584564803 : Nat.Prime 4353861596170690667575550484357142297584564803 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 37, 5505713, 3811955011, 9844277580119, 40681754357567] }])
    [prime_2, prime_7, prime_37, prime_5505713, prime_3811955011, prime_9844277580119, prime_40681754357567]

private theorem prime_38450461327289239258122495579667680507795863717 : Nat.Prime 38450461327289239258122495579667680507795863717 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 11, 40193, 4499273, 55054301, 87773791136882343807688351] }])
    [prime_2, prime_11, prime_40193, prime_4499273, prime_55054301, prime_87773791136882343807688351]

private theorem prime_294710684614833040822713097597465203383478708991 : Nat.Prime 294710684614833040822713097597465203383478708991 := by
  primality (cert := .witnesses [.lucas { root := 6, primeFactors := [2, 3, 5, 19, 23, 139, 365473, 784038791, 188132699053539041681898539] }])
    [prime_2, prime_3, prime_5, prime_19, prime_23, prime_139, prime_365473, prime_784038791, prime_188132699053539041681898539]

private theorem prime_1761917022665818595863556567855975604976145599241 : Nat.Prime 1761917022665818595863556567855975604976145599241 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 107, 1531, 2371, 39829, 45521227639, 62549172628733163298493] }])
    [prime_2, prime_5, prime_107, prime_1531, prime_2371, prime_39829, prime_45521227639, prime_62549172628733163298493]

private theorem prime_3374948313510315693205237485089225293068192983891 : Nat.Prime 3374948313510315693205237485089225293068192983891 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 59, 4129, 70411060116013297943, 19675661775892873533193] }])
    [prime_2, prime_5, prime_59, prime_4129, prime_70411060116013297943, prime_19675661775892873533193]

private theorem prime_6194248703260359691102480196382957834590752399223 : Nat.Prime 6194248703260359691102480196382957834590752399223 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 29, 47, 97, 14747, 6579421, 241434703923132836908859374841623] }])
    [prime_2, prime_29, prime_47, prime_97, prime_14747, prime_6579421, prime_241434703923132836908859374841623]

private theorem prime_6749896627020631386410474970178450586136385967783 : Nat.Prime 6749896627020631386410474970178450586136385967783 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3374948313510315693205237485089225293068192983891] }])
    [prime_2, prime_3374948313510315693205237485089225293068192983891]

private theorem prime_36668007493474012752399646080391690453080900991613 : Nat.Prime 36668007493474012752399646080391690453080900991613 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 11, 13, 383, 23934090899, 171733557353, 40721184886701170073421] }])
    [prime_2, prime_11, prime_13, prime_383, prime_23934090899, prime_171733557353, prime_40721184886701170073421]

private theorem prime_139187659065396629055841392878741826633419374504579 : Nat.Prime 139187659065396629055841392878741826633419374504579 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 9857, 11728416559104797, 22295788290028023187553755183] }])
    [prime_2, prime_3, prime_9857, prime_11728416559104797, prime_22295788290028023187553755183]

private theorem prime_1271678946846363413288027651387020522761781469603059 : Nat.Prime 1271678946846363413288027651387020522761781469603059 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 23, 71, 241, 106921, 6529487, 539637671397211, 1429481932745436223] }])
    [prime_2, prime_3, prime_23, prime_71, prime_241, prime_106921, prime_6529487, prime_539637671397211, prime_1429481932745436223]

private theorem prime_1454196447398079028742192782823031676804839565776941 : Nat.Prime 1454196447398079028742192782823031676804839565776941 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 31, 61, 38450461327289239258122495579667680507795863717] }])
    [prime_2, prime_5, prime_31, prime_61, prime_38450461327289239258122495579667680507795863717]

private theorem prime_45024763619990995506528590724898695843313822602431339 : Nat.Prime 45024763619990995506528590724898695843313822602431339 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 7, 293, 2967382821682375391987, 3698981908496563538334808637] }])
    [prime_2, prime_7, prime_293, prime_2967382821682375391987, prime_3698981908496563538334808637]

private theorem prime_215424386040499785738905644118914263188280913399396813 : Nat.Prime 215424386040499785738905644118914263188280913399396813 := by
  primality (cert := .witnesses [.lucas { root := 5, primeFactors := [2, 3, 197, 239, 1481, 216530773, 1640139724969, 241642156918656757437917] }])
    [prime_2, prime_3, prime_197, prime_239, prime_1481, prime_216530773, prime_1640139724969, prime_241642156918656757437917]

private theorem prime_1160092807424593975174013921113689111972157772621809757 : Nat.Prime 1160092807424593975174013921113689111972157772621809757 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 31163533386231435709306291, 9306492889034384639357270029] }])
    [prime_2, prime_31163533386231435709306291, prime_9306492889034384639357270029]

private theorem prime_1187648456057007162232779097387173767363420427553445441 : Nat.Prime 1187648456057007162232779097387173767363420427553445441 := by
  primality (cert := .witnesses [.lucas { root := 3, primeFactors := [2, 5, 7, 47, 2591, 4353861596170690667575550484357142297584564803] }])
    [prime_2, prime_5, prime_7, prime_47, prime_2591, prime_4353861596170690667575550484357142297584564803]

private theorem prime_5263157894736842209473684210526316477263157894736843619 : Nat.Prime 5263157894736842209473684210526316477263157894736843619 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 7, 11, 6949, 819035216627, 285944334375598337130734239460815999] }])
    [prime_2, prime_3, prime_7, prime_11, prime_6949, prime_819035216627, prime_285944334375598337130734239460815999]

private theorem prime_9433962264150943701886792452830191980377358490566049621 : Nat.Prime 9433962264150943701886792452830191980377358490566049621 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 3, 5, 7, 389, 907, 16167887342161, 1312542657636373210216832047041529] }])
    [prime_2, prime_3, prime_5, prime_7, prime_389, prime_907, prime_16167887342161, prime_1312542657636373210216832047041529]

private theorem prime_100000000000000003720000000000000046128000000000000190651 : Nat.Prime 100000000000000003720000000000000046128000000000000190651 := by
  primality (cert := .witnesses [.lucas { root := 2, primeFactors := [2, 5, 379, 607, 11807458601, 736284508682742314451747640390872415321] }])
    [prime_2, prime_5, prime_379, prime_607, prime_11807458601, prime_736284508682742314451747640390872415321]

private theorem z_pos_1 (x y : ℤ) : x^3+y^3+(10000000000000000001:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000001) (factors := [23, 23, 1181, 1801, 1879, 472992154780007014687741096600552489796295397]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_23, prime_23, prime_1181, prime_1801, prime_1879, prime_472992154780007014687741096600552489796295397, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_3 (x y : ℤ) : x^3+y^3+(-10000000000000000003:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000003) (factors := [23, 181, 211, 29863, 4798989825055906043903, 7943792115876860313934333]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_23, prime_181, prime_211, prime_29863, prime_4798989825055906043903, prime_7943792115876860313934333, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_4 (x y : ℤ) : x^3+y^3+(10000000000000000004:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000004) (factors := [2, 5, 5, 229, 51261379201, 235074455284844477681, 7247676294857717037251]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_5, prime_5, prime_229, prime_51261379201, prime_235074455284844477681, prime_7247676294857717037251, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_9 (x y : ℤ) : x^3+y^3+(-10000000000000000009:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000009) (factors := [19, 1004221, 436439480219666491433, 120086191132872757931474643029]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_19, prime_1004221, prime_436439480219666491433, prime_120086191132872757931474643029, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_13 (x y : ℤ) : x^3+y^3+(10000000000000000013:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000013) (factors := [41, 89, 307, 664529, 25233735959, 1710906597572093, 31114725039669738547]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_41, prime_89, prime_307, prime_664529, prime_25233735959, prime_1710906597572093, prime_31114725039669738547, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_18 (x y : ℤ) : x^3+y^3+(-10000000000000000018:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000018) (factors := [2, 11, 211, 215424386040499785738905644118914263188280913399396813]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_11, prime_211, prime_215424386040499785738905644118914263188280913399396813, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_19 (x y : ℤ) : x^3+y^3+(10000000000000000019:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000019) (factors := [5, 82483, 5190110739061, 586251408063791101, 796902197119382615623]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_5, prime_82483, prime_5190110739061, prime_586251408063791101, prime_796902197119382615623, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_21 (x y : ℤ) : x^3+y^3+(-10000000000000000021:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000021) (factors := [5, 5, 5, 5, 5, 89, 15973, 43766792433758111411, 5143144907223462196121419109]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_5, prime_5, prime_5, prime_5, prime_5, prime_89, prime_15973, prime_43766792433758111411, prime_5143144907223462196121419109, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_22 (x y : ℤ) : x^3+y^3+(10000000000000000022:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000022) (factors := [2, 431, 1160092807424593975174013921113689111972157772621809757]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_431, prime_1160092807424593975174013921113689111972157772621809757, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_24 (x y : ℤ) : x^3+y^3+(-10000000000000000024:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000024) (factors := [2, 16061, 17669, 1761917022665818595863556567855975604976145599241]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_16061, prime_17669, prime_1761917022665818595863556567855975604976145599241, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_25 (x y : ℤ) : x^3+y^3+(10000000000000000025:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000025) (factors := [929, 159473, 6749896627020631386410474970178450586136385967783]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_929, prime_159473, prime_6749896627020631386410474970178450586136385967783, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_30 (x y : ℤ) : x^3+y^3+(-10000000000000000030:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000030) (factors := [2, 1013919507334978087, 493135792716147357863898385429374055811]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_1013919507334978087, prime_493135792716147357863898385429374055811, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_34 (x y : ℤ) : x^3+y^3+(10000000000000000034:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000034) (factors := [2, 5, 2221, 45024763619990995506528590724898695843313822602431339]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_5, prime_2221, prime_45024763619990995506528590724898695843313822602431339, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_39 (x y : ℤ) : x^3+y^3+(-10000000000000000039:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000039) (factors := [1044619, 3808001357081, 251388255843157574082560649419464520147]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_1044619, prime_3808001357081, prime_251388255843157574082560649419464520147, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_40 (x y : ℤ) : x^3+y^3+(10000000000000000040:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000040) (factors := [2, 29, 7247126127611210431519, 2379064336227843720753580395165293]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_29, prime_7247126127611210431519, prime_2379064336227843720753580395165293, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_42 (x y : ℤ) : x^3+y^3+(-10000000000000000042:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000042) (factors := [2, 1031, 89189, 249167942857, 21822669621025437945920900307909707927]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_1031, prime_89189, prime_249167942857, prime_21822669621025437945920900307909707927, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_43 (x y : ℤ) : x^3+y^3+(10000000000000000043:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000043) (factors := [17, 23638839835777, 2488427089502770379620570664240050424389777]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_17, prime_23638839835777, prime_2488427089502770379620570664240050424389777, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_45 (x y : ℤ) : x^3+y^3+(-10000000000000000045:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000045) (factors := [8467, 1052519235013, 112212283125426861484157226343289292343609]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_8467, prime_1052519235013, prime_112212283125426861484157226343289292343609, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_46 (x y : ℤ) : x^3+y^3+(10000000000000000046:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000046) (factors := [2, 160081, 305290673, 4381789039, 2334883492874075436752948849671373]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_160081, prime_305290673, prime_4381789039, prime_2334883492874075436752948849671373, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_51 (x y : ℤ) : x^3+y^3+(-10000000000000000051:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000051) (factors := [5, 11, 12503, 1454196447398079028742192782823031676804839565776941]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_5, prime_11, prime_12503, prime_1454196447398079028742192782823031676804839565776941, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_55 (x y : ℤ) : x^3+y^3+(10000000000000000055:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000055) (factors := [4198838776908691, 238161085274207532887920315503093489421271]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_4198838776908691, prime_238161085274207532887920315503093489421271, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_60 (x y : ℤ) : x^3+y^3+(-10000000000000000060:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000060) (factors := [2, 683, 689269393474878725410241, 1062087521365893764794464830219]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_683, prime_689269393474878725410241, prime_1062087521365893764794464830219, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_61 (x y : ℤ) : x^3+y^3+(10000000000000000061:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000061) (factors := [11, 47, 599, 393413, 3278055857, 2503903448345880856288485368889004189]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_11, prime_47, prime_599, prime_393413, prime_3278055857, prime_2503903448345880856288485368889004189, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_63 (x y : ℤ) : x^3+y^3+(-10000000000000000063:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000063) (factors := [29, 27847, 11189841521, 84838242713431, 1304391581691663426332752597]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_29, prime_27847, prime_11189841521, prime_84838242713431, prime_1304391581691663426332752597, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_64 (x y : ℤ) : x^3+y^3+(10000000000000000064:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000064) (factors := [2, 5, 191, 4363, 14347, 21821, 60493, 1035032137, 6121906817230227457421419373]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_5, prime_191, prime_4363, prime_14347, prime_21821, prime_60493, prime_1035032137, prime_6121906817230227457421419373, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_66 (x y : ℤ) : x^3+y^3+(-10000000000000000066:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000066) (factors := [2, 5, 19, 5263157894736842209473684210526316477263157894736843619]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_5, prime_19, prime_5263157894736842209473684210526316477263157894736843619, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_67 (x y : ℤ) : x^3+y^3+(10000000000000000067:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000067) (factors := [3414858089327, 25956655024873, 11281805660142558091224999752719]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_3414858089327, prime_25956655024873, prime_11281805660142558091224999752719, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_72 (x y : ℤ) : x^3+y^3+(-10000000000000000072:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000072) (factors := [2, 23, 2333, 268793945461051, 34666336429889686991195961430613031809]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_23, prime_2333, prime_268793945461051, prime_34666336429889686991195961430613031809, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_76 (x y : ℤ) : x^3+y^3+(10000000000000000076:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000076) (factors := [2, 61, 2801, 6686958737, 1409239848217, 310537106619460598367623638699]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_61, prime_2801, prime_6686958737, prime_1409239848217, prime_310537106619460598367623638699, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_81 (x y : ℤ) : x^3+y^3+(-10000000000000000081:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000081) (factors := [5, 1436909, 139187659065396629055841392878741826633419374504579]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_5, prime_1436909, prime_139187659065396629055841392878741826633419374504579, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_82 (x y : ℤ) : x^3+y^3+(10000000000000000082:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000082) (factors := [2, 13807, 1149279811, 9546554494483744271, 3300640663614376146281081]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_13807, prime_1149279811, prime_9546554494483744271, prime_3300640663614376146281081, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_84 (x y : ℤ) : x^3+y^3+(-10000000000000000084:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000084) (factors := [2, 11, 11, 83, 65155933, 7391188437184512407, 103380421590861773779384673]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_11, prime_11, prime_83, prime_65155933, prime_7391188437184512407, prime_103380421590861773779384673, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_85 (x y : ℤ) : x^3+y^3+(10000000000000000085:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000085) (factors := [19, 1039, 1747, 1777, 867263, 91066693, 206604670206701803811530905178951]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_19, prime_1039, prime_1747, prime_1777, prime_867263, prime_91066693, prime_206604670206701803811530905178951, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_87 (x y : ℤ) : x^3+y^3+(-10000000000000000087:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000087) (factors := [313, 515783, 6194248703260359691102480196382957834590752399223]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_313, prime_515783, prime_6194248703260359691102480196382957834590752399223, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_88 (x y : ℤ) : x^3+y^3+(10000000000000000088:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000088) (factors := [2, 393181, 1271678946846363413288027651387020522761781469603059]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_393181, prime_1271678946846363413288027651387020522761781469603059, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_93 (x y : ℤ) : x^3+y^3+(-10000000000000000093:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000093) (factors := [3393158281, 294710684614833040822713097597465203383478708991]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_3393158281, prime_294710684614833040822713097597465203383478708991, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_97 (x y : ℤ) : x^3+y^3+(10000000000000000097:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000097) (factors := [4093, 465743, 16453537, 7127810107612771261, 4472975565824772091513]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_4093, prime_465743, prime_16453537, prime_7127810107612771261, prime_4472975565824772091513, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_102 (x y : ℤ) : x^3+y^3+(-10000000000000000102:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000102) (factors := [2, 421, 1187648456057007162232779097387173767363420427553445441]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_421, prime_1187648456057007162232779097387173767363420427553445441, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_103 (x y : ℤ) : x^3+y^3+(10000000000000000103:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000103) (factors := [50839, 23919029, 34967147477117, 23517938481625168713689529984419]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_50839, prime_23919029, prime_34967147477117, prime_23517938481625168713689529984419, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_105 (x y : ℤ) : x^3+y^3+(-10000000000000000105:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000105) (factors := [59785493, 64824909609147439, 258025284322543384519614454542257]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_59785493, prime_64824909609147439, prime_258025284322543384519614454542257, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_106 (x y : ℤ) : x^3+y^3+(10000000000000000106:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000106) (factors := [2, 61, 313, 13800737, 964205119896232600349, 1967995580973679893030139]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_61, prime_313, prime_13800737, prime_964205119896232600349, prime_1967995580973679893030139, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_108 (x y : ℤ) : x^3+y^3+(-10000000000000000108:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000108) (factors := [2, 53, 9433962264150943701886792452830191980377358490566049621]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_53, prime_9433962264150943701886792452830191980377358490566049621, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_109 (x y : ℤ) : x^3+y^3+(10000000000000000109:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000109) (factors := [5, 4463, 166799, 160005724907991899, 1679090654706576081276965528741]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_5, prime_4463, prime_166799, prime_160005724907991899, prime_1679090654706576081276965528741, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_114 (x y : ℤ) : x^3+y^3+(-10000000000000000114:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000114) (factors := [2, 47, 179, 307, 16201673, 225042442921, 53095344600632489279481430824043]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_47, prime_179, prime_307, prime_16201673, prime_225042442921, prime_53095344600632489279481430824043, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_118 (x y : ℤ) : x^3+y^3+(10000000000000000118:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000118) (factors := [2, 421, 1483, 609303719034692009, 1314355747271930081520716037054557]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_421, prime_1483, prime_609303719034692009, prime_1314355747271930081520716037054557, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_123 (x y : ℤ) : x^3+y^3+(-10000000000000000123:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000123) (factors := [19, 1184744750656369110401693, 44424403584155672970130317933443]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_19, prime_1184744750656369110401693, prime_44424403584155672970130317933443, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_124 (x y : ℤ) : x^3+y^3+(10000000000000000124:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000124) (factors := [2, 5, 100000000000000003720000000000000046128000000000000190651]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_5, prime_100000000000000003720000000000000046128000000000000190651, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_neg_126 (x y : ℤ) : x^3+y^3+(-10000000000000000126:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := -10000000000000000126) (factors := [2, 5, 2727173, 36668007493474012752399646080391690453080900991613]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_2, prime_5, prime_2727173, prime_36668007493474012752399646080391690453080900991613, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private theorem z_pos_127 (x y : ℤ) : x^3+y^3+(10000000000000000127:ℤ)^3 ≠ 114 :=
  exclude_by_factors (z := 10000000000000000127) (factors := [11, 29, 29, 409, 548001149, 26984839187069, 17872557694074308203773625711]) (by
    simp only [List.forall_mem_cons]
    exact ⟨prime_11, prime_29, prime_29, prime_409, prime_548001149, prime_26984839187069, prime_17872557694074308203773625711, List.forall_mem_nil _⟩)
    (by decide) (by decide +kernel) x y

private def admissible : List ℤ :=
  [10000000000000000001, -10000000000000000003, 10000000000000000004, -10000000000000000009, 10000000000000000013, -10000000000000000018, 10000000000000000019, -10000000000000000021, 10000000000000000022, -10000000000000000024, 10000000000000000025, -10000000000000000030, 10000000000000000034, -10000000000000000039, 10000000000000000040, -10000000000000000042, 10000000000000000043, -10000000000000000045, 10000000000000000046, -10000000000000000051, 10000000000000000055, -10000000000000000060, 10000000000000000061, -10000000000000000063, 10000000000000000064, -10000000000000000066, 10000000000000000067, -10000000000000000072, 10000000000000000076, -10000000000000000081, 10000000000000000082, -10000000000000000084, 10000000000000000085, -10000000000000000087, 10000000000000000088, -10000000000000000093, 10000000000000000097, -10000000000000000102, 10000000000000000103, -10000000000000000105, 10000000000000000106, -10000000000000000108, 10000000000000000109, -10000000000000000114, 10000000000000000118, -10000000000000000123, 10000000000000000124, -10000000000000000126, 10000000000000000127]

private theorem certified (z : ℤ) (hz : z ∈ admissible) (x y : ℤ) :
    x^3+y^3+z^3 ≠ 114 := by
  simp only [admissible, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact z_pos_1 x y
  · exact z_neg_3 x y
  · exact z_pos_4 x y
  · exact z_neg_9 x y
  · exact z_pos_13 x y
  · exact z_neg_18 x y
  · exact z_pos_19 x y
  · exact z_neg_21 x y
  · exact z_pos_22 x y
  · exact z_neg_24 x y
  · exact z_pos_25 x y
  · exact z_neg_30 x y
  · exact z_pos_34 x y
  · exact z_neg_39 x y
  · exact z_pos_40 x y
  · exact z_neg_42 x y
  · exact z_pos_43 x y
  · exact z_neg_45 x y
  · exact z_pos_46 x y
  · exact z_neg_51 x y
  · exact z_pos_55 x y
  · exact z_neg_60 x y
  · exact z_pos_61 x y
  · exact z_neg_63 x y
  · exact z_pos_64 x y
  · exact z_neg_66 x y
  · exact z_pos_67 x y
  · exact z_neg_72 x y
  · exact z_pos_76 x y
  · exact z_neg_81 x y
  · exact z_pos_82 x y
  · exact z_neg_84 x y
  · exact z_pos_85 x y
  · exact z_neg_87 x y
  · exact z_pos_88 x y
  · exact z_neg_93 x y
  · exact z_pos_97 x y
  · exact z_neg_102 x y
  · exact z_pos_103 x y
  · exact z_neg_105 x y
  · exact z_pos_106 x y
  · exact z_neg_108 x y
  · exact z_pos_109 x y
  · exact z_neg_114 x y
  · exact z_pos_118 x y
  · exact z_neg_123 x y
  · exact z_pos_124 x y
  · exact z_neg_126 x y
  · exact z_pos_127 x y

private def coordinate (i : Fin 128) (negative : Bool) : ℤ :=
  if negative then -(10000000000000000001 + (i.val : ℤ)) else 10000000000000000001 + i.val

private theorem coverage : ∀ (i : Fin 128) (s : Bool),
    localAllowed (coordinate i s) = true → coordinate i s ∈ admissible := by decide

/-- Every pair of integers is excluded for each of the 256 signed coordinates in this interval. -/
theorem exclude_interval (x y z : ℤ) (hl : 10000000000000000000 < |z|)
    (hu : |z| ≤ 10000000000000000128) : x^3+y^3+z^3 ≠ 114 := by
  intro h
  have hc : ∃ (i : Fin 128) (s : Bool), coordinate i s = z := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz] at hl hu
      let i : Fin 128 := ⟨(z-10000000000000000001).toNat, by omega⟩
      exact ⟨i, false, by simp [coordinate, i]; omega⟩
    · rw [abs_of_neg (by omega : z < 0)] at hl hu
      let i : Fin 128 := ⟨(-z-10000000000000000001).toNat, by omega⟩
      exact ⟨i, true, by simp [coordinate, i]; omega⟩
  obtain ⟨i, s, rfl⟩ := hc
  exact certified _ (coverage i s (local_coordinate_pass h)) x y h

end ThreeCubes114.CoordinateCertificate
