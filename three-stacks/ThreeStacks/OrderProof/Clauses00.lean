import ThreeStacks.CertificateBase

/- Generated natural-deduction proof. See verify/generate_order_proof.py. -/
set_option maxRecDepth 15000
set_option maxHeartbeats 8000000

namespace ThreeStacks.OrderProof

theorem c33 (w : Witness) : Before w false 2 1 → Before w false 11 2 → Before w false 1 11 → False :=
  fun z0 z1 z2 => cycle w false 2 1 11 z0 z2 z1

theorem c65 (w : Witness) : Before w false 2 1 → Before w false 19 2 → Before w false 1 19 → False :=
  fun z0 z1 z2 => cycle w false 2 1 19 z0 z2 z1

theorem c101 (w : Witness) : Before w false 3 1 → Before w false 10 3 → Before w false 1 10 → False :=
  fun z0 z1 z2 => cycle w false 3 1 10 z0 z2 z1

theorem c103 (w : Witness) : Before w true 3 1 → Before w true 10 3 → Before w true 1 10 → False :=
  fun z0 z1 z2 => cycle w true 3 1 10 z0 z2 z1

theorem c105 (w : Witness) : Before w false 3 1 → Before w false 11 3 → Before w false 1 11 → False :=
  fun z0 z1 z2 => cycle w false 3 1 11 z0 z2 z1

theorem c135 (w : Witness) : Before w true 3 1 → Before w true 18 3 → Before w true 1 18 → False :=
  fun z0 z1 z2 => cycle w true 3 1 18 z0 z2 z1

theorem c137 (w : Witness) : Before w false 3 1 → Before w false 19 3 → Before w false 1 19 → False :=
  fun z0 z1 z2 => cycle w false 3 1 19 z0 z2 z1

theorem c249 (w : Witness) : Before w false 5 1 → Before w false 14 5 → Before w false 1 14 → False :=
  fun z0 z1 z2 => cycle w false 5 1 14 z0 z2 z1

theorem c277 (w : Witness) : Before w false 5 1 → Before w false 21 5 → Before w false 1 21 → False :=
  fun z0 z1 z2 => cycle w false 5 1 21 z0 z2 z1

theorem c279 (w : Witness) : Before w true 5 1 → Before w true 21 5 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 5 1 21 z0 z2 z1

theorem c283 (w : Witness) : Before w true 6 1 → Before w true 7 6 → Before w true 1 7 → False :=
  fun z0 z1 z2 => cycle w true 6 1 7 z0 z2 z1

theorem c299 (w : Witness) : Before w true 6 1 → Before w true 11 6 → Before w true 1 11 → False :=
  fun z0 z1 z2 => cycle w true 6 1 11 z0 z2 z1

theorem c301 (w : Witness) : Before w false 6 1 → Before w false 12 6 → Before w false 1 12 → False :=
  fun z0 z1 z2 => cycle w false 6 1 12 z0 z2 z1

theorem c309 (w : Witness) : Before w false 6 1 → Before w false 14 6 → Before w false 1 14 → False :=
  fun z0 z1 z2 => cycle w false 6 1 14 z0 z2 z1

theorem c319 (w : Witness) : Before w true 6 1 → Before w true 16 6 → Before w true 1 16 → False :=
  fun z0 z1 z2 => cycle w true 6 1 16 z0 z2 z1

theorem c343 (w : Witness) : Before w true 7 1 → Before w true 8 7 → Before w true 1 8 → False :=
  fun z0 z1 z2 => cycle w true 7 1 8 z0 z2 z1

theorem c349 (w : Witness) : Before w false 7 1 → Before w false 10 7 → Before w false 1 10 → False :=
  fun z0 z1 z2 => cycle w false 7 1 10 z0 z2 z1

theorem c359 (w : Witness) : Before w true 7 1 → Before w true 12 7 → Before w true 1 12 → False :=
  fun z0 z1 z2 => cycle w true 7 1 12 z0 z2 z1

theorem c375 (w : Witness) : Before w true 7 1 → Before w true 16 7 → Before w true 1 16 → False :=
  fun z0 z1 z2 => cycle w true 7 1 16 z0 z2 z1

theorem c378 (w : Witness) : Before w false 1 7 → Before w false 7 17 → Before w false 17 1 → False :=
  fun z0 z1 z2 => cycle w false 1 7 17 z0 z1 z2

theorem c385 (w : Witness) : Before w false 7 1 → Before w false 19 7 → Before w false 1 19 → False :=
  fun z0 z1 z2 => cycle w false 7 1 19 z0 z2 z1

theorem c403 (w : Witness) : Before w true 8 1 → Before w true 10 8 → Before w true 1 10 → False :=
  fun z0 z1 z2 => cycle w true 8 1 10 z0 z2 z1

theorem c410 (w : Witness) : Before w false 1 8 → Before w false 8 12 → Before w false 12 1 → False :=
  fun z0 z1 z2 => cycle w false 1 8 12 z0 z1 z2

theorem c419 (w : Witness) : Before w true 8 1 → Before w true 14 8 → Before w true 1 14 → False :=
  fun z0 z1 z2 => cycle w true 8 1 14 z0 z2 z1

theorem c427 (w : Witness) : Before w true 8 1 → Before w true 16 8 → Before w true 1 16 → False :=
  fun z0 z1 z2 => cycle w true 8 1 16 z0 z2 z1

theorem c433 (w : Witness) : Before w false 8 1 → Before w false 18 8 → Before w false 1 18 → False :=
  fun z0 z1 z2 => cycle w false 8 1 18 z0 z2 z1

theorem c445 (w : Witness) : Before w false 8 1 → Before w false 21 8 → Before w false 1 21 → False :=
  fun z0 z1 z2 => cycle w false 8 1 21 z0 z2 z1

theorem c447 (w : Witness) : Before w true 8 1 → Before w true 21 8 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 8 1 21 z0 z2 z1

theorem c450 (w : Witness) : Before w false 1 9 → Before w false 9 10 → Before w false 10 1 → False :=
  fun z0 z1 z2 => cycle w false 1 9 10 z0 z1 z2

theorem c495 (w : Witness) : Before w true 9 1 → Before w true 21 9 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 9 1 21 z0 z2 z1

theorem c499 (w : Witness) : Before w true 10 1 → Before w true 11 10 → Before w true 1 11 → False :=
  fun z0 z1 z2 => cycle w true 10 1 11 z0 z2 z1

theorem c510 (w : Witness) : Before w false 1 10 → Before w false 10 14 → Before w false 14 1 → False :=
  fun z0 z1 z2 => cycle w false 1 10 14 z0 z1 z2

theorem c519 (w : Witness) : Before w true 10 1 → Before w true 16 10 → Before w true 1 16 → False :=
  fun z0 z1 z2 => cycle w true 10 1 16 z0 z2 z1

theorem c533 (w : Witness) : Before w false 10 1 → Before w false 20 10 → Before w false 1 20 → False :=
  fun z0 z1 z2 => cycle w false 10 1 20 z0 z2 z1

theorem c537 (w : Witness) : Before w false 10 1 → Before w false 21 10 → Before w false 1 21 → False :=
  fun z0 z1 z2 => cycle w false 10 1 21 z0 z2 z1

theorem c539 (w : Witness) : Before w true 10 1 → Before w true 21 10 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 10 1 21 z0 z2 z1

theorem c542 (w : Witness) : Before w false 1 11 → Before w false 11 12 → Before w false 12 1 → False :=
  fun z0 z1 z2 => cycle w false 1 11 12 z0 z1 z2

theorem c543 (w : Witness) : Before w true 11 1 → Before w true 12 11 → Before w true 1 12 → False :=
  fun z0 z1 z2 => cycle w true 11 1 12 z0 z2 z1

theorem c551 (w : Witness) : Before w true 11 1 → Before w true 14 11 → Before w true 1 14 → False :=
  fun z0 z1 z2 => cycle w true 11 1 14 z0 z2 z1

theorem c569 (w : Witness) : Before w false 11 1 → Before w false 19 11 → Before w false 1 19 → False :=
  fun z0 z1 z2 => cycle w false 11 1 19 z0 z2 z1

theorem c577 (w : Witness) : Before w false 11 1 → Before w false 21 11 → Before w false 1 21 → False :=
  fun z0 z1 z2 => cycle w false 11 1 21 z0 z2 z1

theorem c579 (w : Witness) : Before w true 11 1 → Before w true 21 11 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 11 1 21 z0 z2 z1

theorem c581 (w : Witness) : Before w false 12 1 → Before w false 13 12 → Before w false 1 13 → False :=
  fun z0 z1 z2 => cycle w false 12 1 13 z0 z2 z1

theorem c583 (w : Witness) : Before w true 12 1 → Before w true 13 12 → Before w true 1 13 → False :=
  fun z0 z1 z2 => cycle w true 12 1 13 z0 z2 z1

theorem c591 (w : Witness) : Before w true 12 1 → Before w true 15 12 → Before w true 1 15 → False :=
  fun z0 z1 z2 => cycle w true 12 1 15 z0 z2 z1

theorem c595 (w : Witness) : Before w true 12 1 → Before w true 16 12 → Before w true 1 16 → False :=
  fun z0 z1 z2 => cycle w true 12 1 16 z0 z2 z1

theorem c597 (w : Witness) : Before w false 12 1 → Before w false 17 12 → Before w false 1 17 → False :=
  fun z0 z1 z2 => cycle w false 12 1 17 z0 z2 z1

theorem c601 (w : Witness) : Before w false 12 1 → Before w false 18 12 → Before w false 1 18 → False :=
  fun z0 z1 z2 => cycle w false 12 1 18 z0 z2 z1

theorem c605 (w : Witness) : Before w false 12 1 → Before w false 19 12 → Before w false 1 19 → False :=
  fun z0 z1 z2 => cycle w false 12 1 19 z0 z2 z1

theorem c613 (w : Witness) : Before w false 12 1 → Before w false 21 12 → Before w false 1 21 → False :=
  fun z0 z1 z2 => cycle w false 12 1 21 z0 z2 z1

theorem c615 (w : Witness) : Before w true 12 1 → Before w true 21 12 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 12 1 21 z0 z2 z1

theorem c641 (w : Witness) : Before w false 13 1 → Before w false 20 13 → Before w false 1 20 → False :=
  fun z0 z1 z2 => cycle w false 13 1 20 z0 z2 z1

theorem c659 (w : Witness) : Before w true 14 1 → Before w true 17 14 → Before w true 1 17 → False :=
  fun z0 z1 z2 => cycle w true 14 1 17 z0 z2 z1

theorem c661 (w : Witness) : Before w false 14 1 → Before w false 18 14 → Before w false 1 18 → False :=
  fun z0 z1 z2 => cycle w false 14 1 18 z0 z2 z1

theorem c663 (w : Witness) : Before w true 14 1 → Before w true 18 14 → Before w true 1 18 → False :=
  fun z0 z1 z2 => cycle w true 14 1 18 z0 z2 z1

theorem c671 (w : Witness) : Before w true 14 1 → Before w true 20 14 → Before w true 1 20 → False :=
  fun z0 z1 z2 => cycle w true 14 1 20 z0 z2 z1

theorem c673 (w : Witness) : Before w false 14 1 → Before w false 21 14 → Before w false 1 21 → False :=
  fun z0 z1 z2 => cycle w false 14 1 21 z0 z2 z1

theorem c727 (w : Witness) : Before w true 17 1 → Before w true 19 17 → Before w true 1 19 → False :=
  fun z0 z1 z2 => cycle w true 17 1 19 z0 z2 z1

theorem c738 (w : Witness) : Before w false 1 18 → Before w false 18 19 → Before w false 19 1 → False :=
  fun z0 z1 z2 => cycle w false 1 18 19 z0 z1 z2

theorem c739 (w : Witness) : Before w true 18 1 → Before w true 19 18 → Before w true 1 19 → False :=
  fun z0 z1 z2 => cycle w true 18 1 19 z0 z2 z1

theorem c743 (w : Witness) : Before w true 18 1 → Before w true 20 18 → Before w true 1 20 → False :=
  fun z0 z1 z2 => cycle w true 18 1 20 z0 z2 z1

theorem c747 (w : Witness) : Before w true 18 1 → Before w true 21 18 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 18 1 21 z0 z2 z1

theorem c755 (w : Witness) : Before w true 19 1 → Before w true 21 19 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 19 1 21 z0 z2 z1

theorem c758 (w : Witness) : Before w false 1 20 → Before w false 20 21 → Before w false 21 1 → False :=
  fun z0 z1 z2 => cycle w false 1 20 21 z0 z1 z2

theorem c759 (w : Witness) : Before w true 20 1 → Before w true 21 20 → Before w true 1 21 → False :=
  fun z0 z1 z2 => cycle w true 20 1 21 z0 z2 z1

theorem c763 (w : Witness) : Before w true 3 2 → Before w true 4 3 → Before w true 2 4 → False :=
  fun z0 z1 z2 => cycle w true 3 2 4 z0 z2 z1

theorem c770 (w : Witness) : Before w false 2 3 → Before w false 3 6 → Before w false 6 2 → False :=
  fun z0 z1 z2 => cycle w false 2 3 6 z0 z1 z2

theorem c775 (w : Witness) : Before w true 3 2 → Before w true 7 3 → Before w true 2 7 → False :=
  fun z0 z1 z2 => cycle w true 3 2 7 z0 z2 z1

theorem c777 (w : Witness) : Before w false 3 2 → Before w false 8 3 → Before w false 2 8 → False :=
  fun z0 z1 z2 => cycle w false 3 2 8 z0 z2 z1

theorem c778 (w : Witness) : Before w false 2 3 → Before w false 3 8 → Before w false 8 2 → False :=
  fun z0 z1 z2 => cycle w false 2 3 8 z0 z1 z2

theorem c786 (w : Witness) : Before w false 2 3 → Before w false 3 10 → Before w false 10 2 → False :=
  fun z0 z1 z2 => cycle w false 2 3 10 z0 z1 z2

theorem c787 (w : Witness) : Before w true 3 2 → Before w true 10 3 → Before w true 2 10 → False :=
  fun z0 z1 z2 => cycle w true 3 2 10 z0 z2 z1

theorem c790 (w : Witness) : Before w false 2 3 → Before w false 3 11 → Before w false 11 2 → False :=
  fun z0 z1 z2 => cycle w false 2 3 11 z0 z1 z2

theorem c802 (w : Witness) : Before w false 2 3 → Before w false 3 14 → Before w false 14 2 → False :=
  fun z0 z1 z2 => cycle w false 2 3 14 z0 z1 z2

theorem c803 (w : Witness) : Before w true 3 2 → Before w true 14 3 → Before w true 2 14 → False :=
  fun z0 z1 z2 => cycle w true 3 2 14 z0 z2 z1

theorem c822 (w : Witness) : Before w false 2 3 → Before w false 3 19 → Before w false 19 2 → False :=
  fun z0 z1 z2 => cycle w false 2 3 19 z0 z1 z2

theorem c851 (w : Witness) : Before w true 4 2 → Before w true 9 4 → Before w true 2 9 → False :=
  fun z0 z1 z2 => cycle w true 4 2 9 z0 z2 z1

theorem c858 (w : Witness) : Before w false 2 4 → Before w false 4 11 → Before w false 11 2 → False :=
  fun z0 z1 z2 => cycle w false 2 4 11 z0 z1 z2

theorem c861 (w : Witness) : Before w false 4 2 → Before w false 12 4 → Before w false 2 12 → False :=
  fun z0 z1 z2 => cycle w false 4 2 12 z0 z2 z1

theorem c870 (w : Witness) : Before w false 2 4 → Before w false 4 14 → Before w false 14 2 → False :=
  fun z0 z1 z2 => cycle w false 2 4 14 z0 z1 z2

theorem c885 (w : Witness) : Before w false 4 2 → Before w false 18 4 → Before w false 2 18 → False :=
  fun z0 z1 z2 => cycle w false 4 2 18 z0 z2 z1

theorem c897 (w : Witness) : Before w false 4 2 → Before w false 21 4 → Before w false 2 21 → False :=
  fun z0 z1 z2 => cycle w false 4 2 21 z0 z2 z1

theorem c906 (w : Witness) : Before w false 2 5 → Before w false 5 7 → Before w false 7 2 → False :=
  fun z0 z1 z2 => cycle w false 2 5 7 z0 z1 z2

theorem c907 (w : Witness) : Before w true 5 2 → Before w true 7 5 → Before w true 2 7 → False :=
  fun z0 z1 z2 => cycle w true 5 2 7 z0 z2 z1

theorem c975 (w : Witness) : Before w true 6 2 → Before w true 9 6 → Before w true 2 9 → False :=
  fun z0 z1 z2 => cycle w true 6 2 9 z0 z2 z1

theorem c1029 (w : Witness) : Before w false 7 2 → Before w false 9 7 → Before w false 2 9 → False :=
  fun z0 z1 z2 => cycle w false 7 2 9 z0 z2 z1

theorem c1069 (w : Witness) : Before w false 7 2 → Before w false 19 7 → Before w false 2 19 → False :=
  fun z0 z1 z2 => cycle w false 7 2 19 z0 z2 z1

theorem c1083 (w : Witness) : Before w true 8 2 → Before w true 9 8 → Before w true 2 9 → False :=
  fun z0 z1 z2 => cycle w true 8 2 9 z0 z2 z1

theorem c1094 (w : Witness) : Before w false 2 8 → Before w false 8 12 → Before w false 12 2 → False :=
  fun z0 z1 z2 => cycle w false 2 8 12 z0 z1 z2

theorem c1099 (w : Witness) : Before w true 8 2 → Before w true 13 8 → Before w true 2 13 → False :=
  fun z0 z1 z2 => cycle w true 8 2 13 z0 z2 z1

theorem c1102 (w : Witness) : Before w false 2 8 → Before w false 8 14 → Before w false 14 2 → False :=
  fun z0 z1 z2 => cycle w false 2 8 14 z0 z1 z2

theorem c1122 (w : Witness) : Before w false 2 8 → Before w false 8 19 → Before w false 19 2 → False :=
  fun z0 z1 z2 => cycle w false 2 8 19 z0 z1 z2

theorem c1130 (w : Witness) : Before w false 2 8 → Before w false 8 21 → Before w false 21 2 → False :=
  fun z0 z1 z2 => cycle w false 2 8 21 z0 z1 z2

theorem c1134 (w : Witness) : Before w false 2 9 → Before w false 9 10 → Before w false 10 2 → False :=
  fun z0 z1 z2 => cycle w false 2 9 10 z0 z1 z2

theorem c1141 (w : Witness) : Before w false 9 2 → Before w false 12 9 → Before w false 2 12 → False :=
  fun z0 z1 z2 => cycle w false 9 2 12 z0 z2 z1

theorem c1150 (w : Witness) : Before w false 2 9 → Before w false 9 14 → Before w false 14 2 → False :=
  fun z0 z1 z2 => cycle w false 2 9 14 z0 z1 z2

theorem c1170 (w : Witness) : Before w false 2 9 → Before w false 9 19 → Before w false 19 2 → False :=
  fun z0 z1 z2 => cycle w false 2 9 19 z0 z1 z2

theorem c1189 (w : Witness) : Before w false 10 2 → Before w false 13 10 → Before w false 2 13 → False :=
  fun z0 z1 z2 => cycle w false 10 2 13 z0 z2 z1

theorem c1194 (w : Witness) : Before w false 2 10 → Before w false 10 14 → Before w false 14 2 → False :=
  fun z0 z1 z2 => cycle w false 2 10 14 z0 z1 z2

theorem c1195 (w : Witness) : Before w true 10 2 → Before w true 14 10 → Before w true 2 14 → False :=
  fun z0 z1 z2 => cycle w true 10 2 14 z0 z2 z1

theorem c1211 (w : Witness) : Before w true 10 2 → Before w true 18 10 → Before w true 2 18 → False :=
  fun z0 z1 z2 => cycle w true 10 2 18 z0 z2 z1

theorem c1233 (w : Witness) : Before w false 11 2 → Before w false 14 11 → Before w false 2 14 → False :=
  fun z0 z1 z2 => cycle w false 11 2 14 z0 z2 z1

theorem c1241 (w : Witness) : Before w false 11 2 → Before w false 16 11 → Before w false 2 16 → False :=
  fun z0 z1 z2 => cycle w false 11 2 16 z0 z2 z1

theorem c1261 (w : Witness) : Before w false 11 2 → Before w false 21 11 → Before w false 2 21 → False :=
  fun z0 z1 z2 => cycle w false 11 2 21 z0 z2 z1

theorem c1290 (w : Witness) : Before w false 2 12 → Before w false 12 19 → Before w false 19 2 → False :=
  fun z0 z1 z2 => cycle w false 2 12 19 z0 z1 z2

theorem c1295 (w : Witness) : Before w true 12 2 → Before w true 20 12 → Before w true 2 20 → False :=
  fun z0 z1 z2 => cycle w true 12 2 20 z0 z2 z1

theorem c1298 (w : Witness) : Before w false 2 12 → Before w false 12 21 → Before w false 21 2 → False :=
  fun z0 z1 z2 => cycle w false 2 12 21 z0 z1 z2

theorem c1323 (w : Witness) : Before w true 13 2 → Before w true 19 13 → Before w true 2 19 → False :=
  fun z0 z1 z2 => cycle w true 13 2 19 z0 z2 z1

theorem c1339 (w : Witness) : Before w true 14 2 → Before w true 16 14 → Before w true 2 16 → False :=
  fun z0 z1 z2 => cycle w true 14 2 16 z0 z2 z1

theorem c1357 (w : Witness) : Before w false 14 2 → Before w false 21 14 → Before w false 2 21 → False :=
  fun z0 z1 z2 => cycle w false 14 2 21 z0 z2 z1

theorem c1375 (w : Witness) : Before w true 15 2 → Before w true 19 15 → Before w true 2 19 → False :=
  fun z0 z1 z2 => cycle w true 15 2 19 z0 z2 z1

theorem c1415 (w : Witness) : Before w true 17 2 → Before w true 20 17 → Before w true 2 20 → False :=
  fun z0 z1 z2 => cycle w true 17 2 20 z0 z2 z1

theorem c1418 (w : Witness) : Before w false 2 17 → Before w false 17 21 → Before w false 21 2 → False :=
  fun z0 z1 z2 => cycle w false 2 17 21 z0 z1 z2

theorem c1422 (w : Witness) : Before w false 2 18 → Before w false 18 19 → Before w false 19 2 → False :=
  fun z0 z1 z2 => cycle w false 2 18 19 z0 z1 z2

theorem c1431 (w : Witness) : Before w true 18 2 → Before w true 21 18 → Before w true 2 21 → False :=
  fun z0 z1 z2 => cycle w true 18 2 21 z0 z2 z1

theorem c1433 (w : Witness) : Before w false 19 2 → Before w false 20 19 → Before w false 2 20 → False :=
  fun z0 z1 z2 => cycle w false 19 2 20 z0 z2 z1

theorem c1446 (w : Witness) : Before w false 3 4 → Before w false 4 5 → Before w false 5 3 → False :=
  fun z0 z1 z2 => cycle w false 3 4 5 z0 z1 z2

theorem c1447 (w : Witness) : Before w true 4 3 → Before w true 5 4 → Before w true 3 5 → False :=
  fun z0 z1 z2 => cycle w true 4 3 5 z0 z2 z1

theorem c1449 (w : Witness) : Before w false 4 3 → Before w false 6 4 → Before w false 3 6 → False :=
  fun z0 z1 z2 => cycle w false 4 3 6 z0 z2 z1

theorem c1458 (w : Witness) : Before w false 3 4 → Before w false 4 8 → Before w false 8 3 → False :=
  fun z0 z1 z2 => cycle w false 3 4 8 z0 z1 z2

theorem c1491 (w : Witness) : Before w true 4 3 → Before w true 16 4 → Before w true 3 16 → False :=
  fun z0 z1 z2 => cycle w true 4 3 16 z0 z2 z1

theorem c1511 (w : Witness) : Before w true 4 3 → Before w true 21 4 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 4 3 21 z0 z2 z1

theorem c1513 (w : Witness) : Before w false 5 3 → Before w false 6 5 → Before w false 3 6 → False :=
  fun z0 z1 z2 => cycle w false 5 3 6 z0 z2 z1

theorem c1525 (w : Witness) : Before w false 5 3 → Before w false 9 5 → Before w false 3 9 → False :=
  fun z0 z1 z2 => cycle w false 5 3 9 z0 z2 z1

theorem c1527 (w : Witness) : Before w true 5 3 → Before w true 9 5 → Before w true 3 9 → False :=
  fun z0 z1 z2 => cycle w true 5 3 9 z0 z2 z1

theorem c1538 (w : Witness) : Before w false 3 5 → Before w false 5 12 → Before w false 12 3 → False :=
  fun z0 z1 z2 => cycle w false 3 5 12 z0 z1 z2

theorem c1541 (w : Witness) : Before w false 5 3 → Before w false 13 5 → Before w false 3 13 → False :=
  fun z0 z1 z2 => cycle w false 5 3 13 z0 z2 z1

theorem c1553 (w : Witness) : Before w false 5 3 → Before w false 16 5 → Before w false 3 16 → False :=
  fun z0 z1 z2 => cycle w false 5 3 16 z0 z2 z1

theorem c1555 (w : Witness) : Before w true 5 3 → Before w true 16 5 → Before w true 3 16 → False :=
  fun z0 z1 z2 => cycle w true 5 3 16 z0 z2 z1

theorem c1586 (w : Witness) : Before w false 3 6 → Before w false 6 9 → Before w false 9 3 → False :=
  fun z0 z1 z2 => cycle w false 3 6 9 z0 z1 z2

theorem c1590 (w : Witness) : Before w false 3 6 → Before w false 6 10 → Before w false 10 3 → False :=
  fun z0 z1 z2 => cycle w false 3 6 10 z0 z1 z2

theorem c1594 (w : Witness) : Before w false 3 6 → Before w false 6 11 → Before w false 11 3 → False :=
  fun z0 z1 z2 => cycle w false 3 6 11 z0 z1 z2

theorem c1606 (w : Witness) : Before w false 3 6 → Before w false 6 14 → Before w false 14 3 → False :=
  fun z0 z1 z2 => cycle w false 3 6 14 z0 z1 z2

theorem c1626 (w : Witness) : Before w false 3 6 → Before w false 6 19 → Before w false 19 3 → False :=
  fun z0 z1 z2 => cycle w false 3 6 19 z0 z1 z2

theorem c1635 (w : Witness) : Before w true 6 3 → Before w true 21 6 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 6 3 21 z0 z2 z1

theorem c1643 (w : Witness) : Before w true 7 3 → Before w true 9 7 → Before w true 3 9 → False :=
  fun z0 z1 z2 => cycle w true 7 3 9 z0 z2 z1

theorem c1645 (w : Witness) : Before w false 7 3 → Before w false 10 7 → Before w false 3 10 → False :=
  fun z0 z1 z2 => cycle w false 7 3 10 z0 z2 z1

theorem c1671 (w : Witness) : Before w true 7 3 → Before w true 16 7 → Before w true 3 16 → False :=
  fun z0 z1 z2 => cycle w true 7 3 16 z0 z2 z1

theorem c1693 (w : Witness) : Before w false 8 3 → Before w false 9 8 → Before w false 3 9 → False :=
  fun z0 z1 z2 => cycle w false 8 3 9 z0 z2 z1

theorem c1697 (w : Witness) : Before w false 8 3 → Before w false 10 8 → Before w false 3 10 → False :=
  fun z0 z1 z2 => cycle w false 8 3 10 z0 z2 z1

theorem c1709 (w : Witness) : Before w false 8 3 → Before w false 13 8 → Before w false 3 13 → False :=
  fun z0 z1 z2 => cycle w false 8 3 13 z0 z2 z1

theorem c1733 (w : Witness) : Before w false 8 3 → Before w false 19 8 → Before w false 3 19 → False :=
  fun z0 z1 z2 => cycle w false 8 3 19 z0 z2 z1

theorem c1737 (w : Witness) : Before w false 8 3 → Before w false 20 8 → Before w false 3 20 → False :=
  fun z0 z1 z2 => cycle w false 8 3 20 z0 z2 z1

theorem c1754 (w : Witness) : Before w false 3 9 → Before w false 9 12 → Before w false 12 3 → False :=
  fun z0 z1 z2 => cycle w false 3 9 12 z0 z1 z2

theorem c1774 (w : Witness) : Before w false 3 9 → Before w false 9 17 → Before w false 17 3 → False :=
  fun z0 z1 z2 => cycle w false 3 9 17 z0 z1 z2

theorem c1798 (w : Witness) : Before w false 3 10 → Before w false 10 12 → Before w false 12 3 → False :=
  fun z0 z1 z2 => cycle w false 3 10 12 z0 z1 z2

theorem c1799 (w : Witness) : Before w true 10 3 → Before w true 12 10 → Before w true 3 12 → False :=
  fun z0 z1 z2 => cycle w true 10 3 12 z0 z2 z1

theorem c1815 (w : Witness) : Before w true 10 3 → Before w true 16 10 → Before w true 3 16 → False :=
  fun z0 z1 z2 => cycle w true 10 3 16 z0 z2 z1

theorem c1818 (w : Witness) : Before w false 3 10 → Before w false 10 17 → Before w false 17 3 → False :=
  fun z0 z1 z2 => cycle w false 3 10 17 z0 z1 z2

theorem c1823 (w : Witness) : Before w true 10 3 → Before w true 18 10 → Before w true 3 18 → False :=
  fun z0 z1 z2 => cycle w true 10 3 18 z0 z2 z1

theorem c1833 (w : Witness) : Before w false 10 3 → Before w false 21 10 → Before w false 3 21 → False :=
  fun z0 z1 z2 => cycle w false 10 3 21 z0 z2 z1

theorem c1835 (w : Witness) : Before w true 10 3 → Before w true 21 10 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 10 3 21 z0 z2 z1

theorem c1838 (w : Witness) : Before w false 3 11 → Before w false 11 12 → Before w false 12 3 → False :=
  fun z0 z1 z2 => cycle w false 3 11 12 z0 z1 z2

theorem c1843 (w : Witness) : Before w true 11 3 → Before w true 13 11 → Before w true 3 13 → False :=
  fun z0 z1 z2 => cycle w true 11 3 13 z0 z2 z1

theorem c1847 (w : Witness) : Before w true 11 3 → Before w true 14 11 → Before w true 3 14 → False :=
  fun z0 z1 z2 => cycle w true 11 3 14 z0 z2 z1

theorem c1861 (w : Witness) : Before w false 11 3 → Before w false 18 11 → Before w false 3 18 → False :=
  fun z0 z1 z2 => cycle w false 11 3 18 z0 z2 z1

theorem c1867 (w : Witness) : Before w true 11 3 → Before w true 19 11 → Before w true 3 19 → False :=
  fun z0 z1 z2 => cycle w true 11 3 19 z0 z2 z1

theorem c1869 (w : Witness) : Before w false 11 3 → Before w false 20 11 → Before w false 3 20 → False :=
  fun z0 z1 z2 => cycle w false 11 3 20 z0 z2 z1

theorem c1873 (w : Witness) : Before w false 11 3 → Before w false 21 11 → Before w false 3 21 → False :=
  fun z0 z1 z2 => cycle w false 11 3 21 z0 z2 z1

theorem c1875 (w : Witness) : Before w true 11 3 → Before w true 21 11 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 11 3 21 z0 z2 z1

theorem c1885 (w : Witness) : Before w false 12 3 → Before w false 15 12 → Before w false 3 15 → False :=
  fun z0 z1 z2 => cycle w false 12 3 15 z0 z2 z1

theorem c1897 (w : Witness) : Before w false 12 3 → Before w false 18 12 → Before w false 3 18 → False :=
  fun z0 z1 z2 => cycle w false 12 3 18 z0 z2 z1

theorem c1899 (w : Witness) : Before w true 12 3 → Before w true 18 12 → Before w true 3 18 → False :=
  fun z0 z1 z2 => cycle w true 12 3 18 z0 z2 z1

theorem c1901 (w : Witness) : Before w false 12 3 → Before w false 19 12 → Before w false 3 19 → False :=
  fun z0 z1 z2 => cycle w false 12 3 19 z0 z2 z1

theorem c1903 (w : Witness) : Before w true 12 3 → Before w true 19 12 → Before w true 3 19 → False :=
  fun z0 z1 z2 => cycle w true 12 3 19 z0 z2 z1

theorem c1905 (w : Witness) : Before w false 12 3 → Before w false 20 12 → Before w false 3 20 → False :=
  fun z0 z1 z2 => cycle w false 12 3 20 z0 z2 z1

theorem c1909 (w : Witness) : Before w false 12 3 → Before w false 21 12 → Before w false 3 21 → False :=
  fun z0 z1 z2 => cycle w false 12 3 21 z0 z2 z1

theorem c1911 (w : Witness) : Before w true 12 3 → Before w true 21 12 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 12 3 21 z0 z2 z1

theorem c1919 (w : Witness) : Before w true 13 3 → Before w true 15 13 → Before w true 3 15 → False :=
  fun z0 z1 z2 => cycle w true 13 3 15 z0 z2 z1

theorem c1922 (w : Witness) : Before w false 3 13 → Before w false 13 16 → Before w false 16 3 → False :=
  fun z0 z1 z2 => cycle w false 3 13 16 z0 z1 z2

theorem c1926 (w : Witness) : Before w false 3 13 → Before w false 13 17 → Before w false 17 3 → False :=
  fun z0 z1 z2 => cycle w false 3 13 17 z0 z1 z2

theorem c1934 (w : Witness) : Before w false 3 13 → Before w false 13 19 → Before w false 19 3 → False :=
  fun z0 z1 z2 => cycle w false 3 13 19 z0 z1 z2

theorem c1937 (w : Witness) : Before w false 13 3 → Before w false 20 13 → Before w false 3 20 → False :=
  fun z0 z1 z2 => cycle w false 13 3 20 z0 z2 z1

theorem c1947 (w : Witness) : Before w true 14 3 → Before w true 15 14 → Before w true 3 15 → False :=
  fun z0 z1 z2 => cycle w true 14 3 15 z0 z2 z1

theorem c1951 (w : Witness) : Before w true 14 3 → Before w true 16 14 → Before w true 3 16 → False :=
  fun z0 z1 z2 => cycle w true 14 3 16 z0 z2 z1

theorem c1955 (w : Witness) : Before w true 14 3 → Before w true 17 14 → Before w true 3 17 → False :=
  fun z0 z1 z2 => cycle w true 14 3 17 z0 z2 z1

theorem c1963 (w : Witness) : Before w true 14 3 → Before w true 19 14 → Before w true 3 19 → False :=
  fun z0 z1 z2 => cycle w true 14 3 19 z0 z2 z1

theorem c1965 (w : Witness) : Before w false 14 3 → Before w false 20 14 → Before w false 3 20 → False :=
  fun z0 z1 z2 => cycle w false 14 3 20 z0 z2 z1

theorem c1971 (w : Witness) : Before w true 14 3 → Before w true 21 14 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 14 3 21 z0 z2 z1

theorem c1978 (w : Witness) : Before w false 3 15 → Before w false 15 17 → Before w false 17 3 → False :=
  fun z0 z1 z2 => cycle w false 3 15 17 z0 z1 z2

theorem c1982 (w : Witness) : Before w false 3 15 → Before w false 15 18 → Before w false 18 3 → False :=
  fun z0 z1 z2 => cycle w false 3 15 18 z0 z1 z2

theorem c1999 (w : Witness) : Before w true 16 3 → Before w true 17 16 → Before w true 3 17 → False :=
  fun z0 z1 z2 => cycle w true 16 3 17 z0 z2 z1

theorem c2019 (w : Witness) : Before w true 17 3 → Before w true 18 17 → Before w true 3 18 → False :=
  fun z0 z1 z2 => cycle w true 17 3 18 z0 z2 z1

theorem c2021 (w : Witness) : Before w false 17 3 → Before w false 19 17 → Before w false 3 19 → False :=
  fun z0 z1 z2 => cycle w false 17 3 19 z0 z2 z1

theorem c2023 (w : Witness) : Before w true 17 3 → Before w true 19 17 → Before w true 3 19 → False :=
  fun z0 z1 z2 => cycle w true 17 3 19 z0 z2 z1

theorem c2025 (w : Witness) : Before w false 17 3 → Before w false 20 17 → Before w false 3 20 → False :=
  fun z0 z1 z2 => cycle w false 17 3 20 z0 z2 z1

theorem c2029 (w : Witness) : Before w false 17 3 → Before w false 21 17 → Before w false 3 21 → False :=
  fun z0 z1 z2 => cycle w false 17 3 21 z0 z2 z1

theorem c2031 (w : Witness) : Before w true 17 3 → Before w true 21 17 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 17 3 21 z0 z2 z1

theorem c2034 (w : Witness) : Before w false 3 18 → Before w false 18 19 → Before w false 19 3 → False :=
  fun z0 z1 z2 => cycle w false 3 18 19 z0 z1 z2

theorem c2035 (w : Witness) : Before w true 18 3 → Before w true 19 18 → Before w true 3 19 → False :=
  fun z0 z1 z2 => cycle w true 18 3 19 z0 z2 z1

theorem c2041 (w : Witness) : Before w false 18 3 → Before w false 21 18 → Before w false 3 21 → False :=
  fun z0 z1 z2 => cycle w false 18 3 21 z0 z2 z1

theorem c2045 (w : Witness) : Before w false 19 3 → Before w false 20 19 → Before w false 3 20 → False :=
  fun z0 z1 z2 => cycle w false 19 3 20 z0 z2 z1

theorem c2055 (w : Witness) : Before w true 20 3 → Before w true 21 20 → Before w true 3 21 → False :=
  fun z0 z1 z2 => cycle w true 20 3 21 z0 z2 z1

theorem c2058 (w : Witness) : Before w false 4 5 → Before w false 5 6 → Before w false 6 4 → False :=
  fun z0 z1 z2 => cycle w false 4 5 6 z0 z1 z2

theorem c2183 (w : Witness) : Before w true 7 4 → Before w true 8 7 → Before w true 4 8 → False :=
  fun z0 z1 z2 => cycle w true 7 4 8 z0 z2 z1

theorem c2194 (w : Witness) : Before w false 4 7 → Before w false 7 11 → Before w false 11 4 → False :=
  fun z0 z1 z2 => cycle w false 4 7 11 z0 z1 z2

theorem c2202 (w : Witness) : Before w false 4 7 → Before w false 7 13 → Before w false 13 4 → False :=
  fun z0 z1 z2 => cycle w false 4 7 13 z0 z1 z2

theorem c2205 (w : Witness) : Before w false 7 4 → Before w false 14 7 → Before w false 4 14 → False :=
  fun z0 z1 z2 => cycle w false 7 4 14 z0 z2 z1

theorem c2218 (w : Witness) : Before w false 4 7 → Before w false 7 17 → Before w false 17 4 → False :=
  fun z0 z1 z2 => cycle w false 4 7 17 z0 z1 z2

theorem c2230 (w : Witness) : Before w false 4 7 → Before w false 7 20 → Before w false 20 4 → False :=
  fun z0 z1 z2 => cycle w false 4 7 20 z0 z1 z2

theorem c2234 (w : Witness) : Before w false 4 7 → Before w false 7 21 → Before w false 21 4 → False :=
  fun z0 z1 z2 => cycle w false 4 7 21 z0 z1 z2

theorem c2250 (w : Witness) : Before w false 4 8 → Before w false 8 12 → Before w false 12 4 → False :=
  fun z0 z1 z2 => cycle w false 4 8 12 z0 z1 z2

theorem c2295 (w : Witness) : Before w true 9 4 → Before w true 11 9 → Before w true 4 11 → False :=
  fun z0 z1 z2 => cycle w true 9 4 11 z0 z2 z1

theorem c2299 (w : Witness) : Before w true 9 4 → Before w true 12 9 → Before w true 4 12 → False :=
  fun z0 z1 z2 => cycle w true 9 4 12 z0 z2 z1

theorem c2315 (w : Witness) : Before w true 9 4 → Before w true 16 9 → Before w true 4 16 → False :=
  fun z0 z1 z2 => cycle w true 9 4 16 z0 z2 z1

theorem c2322 (w : Witness) : Before w false 4 9 → Before w false 9 18 → Before w false 18 4 → False :=
  fun z0 z1 z2 => cycle w false 4 9 18 z0 z1 z2

theorem c2325 (w : Witness) : Before w false 9 4 → Before w false 19 9 → Before w false 4 19 → False :=
  fun z0 z1 z2 => cycle w false 9 4 19 z0 z2 z1

theorem c2334 (w : Witness) : Before w false 4 9 → Before w false 9 21 → Before w false 21 4 → False :=
  fun z0 z1 z2 => cycle w false 4 9 21 z0 z1 z2

theorem c2346 (w : Witness) : Before w false 4 10 → Before w false 10 13 → Before w false 13 4 → False :=
  fun z0 z1 z2 => cycle w false 4 10 13 z0 z1 z2

theorem c2350 (w : Witness) : Before w false 4 10 → Before w false 10 14 → Before w false 14 4 → False :=
  fun z0 z1 z2 => cycle w false 4 10 14 z0 z1 z2

theorem c2474 (w : Witness) : Before w false 4 13 → Before w false 13 18 → Before w false 18 4 → False :=
  fun z0 z1 z2 => cycle w false 4 13 18 z0 z1 z2

theorem c2481 (w : Witness) : Before w false 13 4 → Before w false 20 13 → Before w false 4 20 → False :=
  fun z0 z1 z2 => cycle w false 13 4 20 z0 z2 z1

theorem c2503 (w : Witness) : Before w true 14 4 → Before w true 18 14 → Before w true 4 18 → False :=
  fun z0 z1 z2 => cycle w true 14 4 18 z0 z2 z1

theorem c2515 (w : Witness) : Before w true 14 4 → Before w true 21 14 → Before w true 4 21 → False :=
  fun z0 z1 z2 => cycle w true 14 4 21 z0 z2 z1

theorem c2539 (w : Witness) : Before w true 15 4 → Before w true 21 15 → Before w true 4 21 → False :=
  fun z0 z1 z2 => cycle w true 15 4 21 z0 z2 z1

theorem c2559 (w : Witness) : Before w true 16 4 → Before w true 21 16 → Before w true 4 21 → False :=
  fun z0 z1 z2 => cycle w true 16 4 21 z0 z2 z1

theorem c2562 (w : Witness) : Before w false 4 17 → Before w false 17 18 → Before w false 18 4 → False :=
  fun z0 z1 z2 => cycle w false 4 17 18 z0 z1 z2

theorem c2575 (w : Witness) : Before w true 17 4 → Before w true 21 17 → Before w true 4 21 → False :=
  fun z0 z1 z2 => cycle w true 17 4 21 z0 z2 z1

theorem c2583 (w : Witness) : Before w true 18 4 → Before w true 20 18 → Before w true 4 20 → False :=
  fun z0 z1 z2 => cycle w true 18 4 20 z0 z2 z1

theorem c2585 (w : Witness) : Before w false 18 4 → Before w false 21 18 → Before w false 4 21 → False :=
  fun z0 z1 z2 => cycle w false 18 4 21 z0 z2 z1

theorem c2587 (w : Witness) : Before w true 18 4 → Before w true 21 18 → Before w true 4 21 → False :=
  fun z0 z1 z2 => cycle w true 18 4 21 z0 z2 z1

theorem c2590 (w : Witness) : Before w false 4 19 → Before w false 19 20 → Before w false 20 4 → False :=
  fun z0 z1 z2 => cycle w false 4 19 20 z0 z1 z2

theorem c2591 (w : Witness) : Before w true 19 4 → Before w true 20 19 → Before w true 4 20 → False :=
  fun z0 z1 z2 => cycle w true 19 4 20 z0 z2 z1

theorem c2594 (w : Witness) : Before w false 4 19 → Before w false 19 21 → Before w false 21 4 → False :=
  fun z0 z1 z2 => cycle w false 4 19 21 z0 z1 z2

theorem c2595 (w : Witness) : Before w true 19 4 → Before w true 21 19 → Before w true 4 21 → False :=
  fun z0 z1 z2 => cycle w true 19 4 21 z0 z2 z1

theorem c2599 (w : Witness) : Before w true 20 4 → Before w true 21 20 → Before w true 4 21 → False :=
  fun z0 z1 z2 => cycle w true 20 4 21 z0 z2 z1

theorem c2626 (w : Witness) : Before w false 5 6 → Before w false 6 13 → Before w false 13 5 → False :=
  fun z0 z1 z2 => cycle w false 5 6 13 z0 z1 z2

theorem c2638 (w : Witness) : Before w false 5 6 → Before w false 6 16 → Before w false 16 5 → False :=
  fun z0 z1 z2 => cycle w false 5 6 16 z0 z1 z2

theorem c2665 (w : Witness) : Before w false 7 5 → Before w false 9 7 → Before w false 5 9 → False :=
  fun z0 z1 z2 => cycle w false 7 5 9 z0 z2 z1

theorem c2718 (w : Witness) : Before w false 5 8 → Before w false 8 9 → Before w false 9 5 → False :=
  fun z0 z1 z2 => cycle w false 5 8 9 z0 z1 z2

theorem c2727 (w : Witness) : Before w true 8 5 → Before w true 11 8 → Before w true 5 11 → False :=
  fun z0 z1 z2 => cycle w true 8 5 11 z0 z2 z1

theorem c2730 (w : Witness) : Before w false 5 8 → Before w false 8 12 → Before w false 12 5 → False :=
  fun z0 z1 z2 => cycle w false 5 8 12 z0 z1 z2

theorem c2731 (w : Witness) : Before w true 8 5 → Before w true 12 8 → Before w true 5 12 → False :=
  fun z0 z1 z2 => cycle w true 8 5 12 z0 z2 z1

theorem c2746 (w : Witness) : Before w false 5 8 → Before w false 8 16 → Before w false 16 5 → False :=
  fun z0 z1 z2 => cycle w false 5 8 16 z0 z1 z2

theorem c2749 (w : Witness) : Before w false 8 5 → Before w false 17 8 → Before w false 5 17 → False :=
  fun z0 z1 z2 => cycle w false 8 5 17 z0 z2 z1

theorem c2751 (w : Witness) : Before w true 8 5 → Before w true 17 8 → Before w true 5 17 → False :=
  fun z0 z1 z2 => cycle w true 8 5 17 z0 z2 z1

theorem c2755 (w : Witness) : Before w true 8 5 → Before w true 18 8 → Before w true 5 18 → False :=
  fun z0 z1 z2 => cycle w true 8 5 18 z0 z2 z1

theorem c2758 (w : Witness) : Before w false 5 8 → Before w false 8 19 → Before w false 19 5 → False :=
  fun z0 z1 z2 => cycle w false 5 8 19 z0 z1 z2

theorem c2807 (w : Witness) : Before w true 9 5 → Before w true 19 9 → Before w true 5 19 → False :=
  fun z0 z1 z2 => cycle w true 9 5 19 z0 z2 z1

theorem c2859 (w : Witness) : Before w true 10 5 → Before w true 21 10 → Before w true 5 21 → False :=
  fun z0 z1 z2 => cycle w true 10 5 21 z0 z2 z1

theorem c2921 (w : Witness) : Before w false 12 5 → Before w false 18 12 → Before w false 5 18 → False :=
  fun z0 z1 z2 => cycle w false 12 5 18 z0 z2 z1

theorem c2922 (w : Witness) : Before w false 5 12 → Before w false 12 18 → Before w false 18 5 → False :=
  fun z0 z1 z2 => cycle w false 5 12 18 z0 z1 z2

theorem c2931 (w : Witness) : Before w true 12 5 → Before w true 20 12 → Before w true 5 20 → False :=
  fun z0 z1 z2 => cycle w true 12 5 20 z0 z2 z1

theorem c2934 (w : Witness) : Before w false 5 12 → Before w false 12 21 → Before w false 21 5 → False :=
  fun z0 z1 z2 => cycle w false 5 12 21 z0 z1 z2

theorem c2954 (w : Witness) : Before w false 5 13 → Before w false 13 18 → Before w false 18 5 → False :=
  fun z0 z1 z2 => cycle w false 5 13 18 z0 z1 z2

theorem c2995 (w : Witness) : Before w true 14 5 → Before w true 21 14 → Before w true 5 21 → False :=
  fun z0 z1 z2 => cycle w true 14 5 21 z0 z2 z1

theorem c3006 (w : Witness) : Before w false 5 15 → Before w false 15 18 → Before w false 18 5 → False :=
  fun z0 z1 z2 => cycle w false 5 15 18 z0 z1 z2

theorem c3011 (w : Witness) : Before w true 15 5 → Before w true 19 15 → Before w true 5 19 → False :=
  fun z0 z1 z2 => cycle w true 15 5 19 z0 z2 z1

theorem c3039 (w : Witness) : Before w true 16 5 → Before w true 21 16 → Before w true 5 21 → False :=
  fun z0 z1 z2 => cycle w true 16 5 21 z0 z2 z1

theorem c3046 (w : Witness) : Before w false 5 17 → Before w false 17 19 → Before w false 19 5 → False :=
  fun z0 z1 z2 => cycle w false 5 17 19 z0 z1 z2

theorem c3050 (w : Witness) : Before w false 5 17 → Before w false 17 20 → Before w false 20 5 → False :=
  fun z0 z1 z2 => cycle w false 5 17 20 z0 z1 z2

theorem c3073 (w : Witness) : Before w false 19 5 → Before w false 21 19 → Before w false 5 21 → False :=
  fun z0 z1 z2 => cycle w false 19 5 21 z0 z2 z1

theorem c3083 (w : Witness) : Before w true 7 6 → Before w true 8 7 → Before w true 6 8 → False :=
  fun z0 z1 z2 => cycle w true 7 6 8 z0 z2 z1

theorem c3118 (w : Witness) : Before w false 6 7 → Before w false 7 17 → Before w false 17 6 → False :=
  fun z0 z1 z2 => cycle w false 6 7 17 z0 z1 z2

theorem c3119 (w : Witness) : Before w true 7 6 → Before w true 17 7 → Before w true 6 17 → False :=
  fun z0 z1 z2 => cycle w true 7 6 17 z0 z2 z1

theorem c3127 (w : Witness) : Before w true 7 6 → Before w true 19 7 → Before w true 6 19 → False :=
  fun z0 z1 z2 => cycle w true 7 6 19 z0 z2 z1

theorem c3129 (w : Witness) : Before w false 7 6 → Before w false 20 7 → Before w false 6 20 → False :=
  fun z0 z1 z2 => cycle w false 7 6 20 z0 z2 z1

theorem c3151 (w : Witness) : Before w true 8 6 → Before w true 12 8 → Before w true 6 12 → False :=
  fun z0 z1 z2 => cycle w true 8 6 12 z0 z2 z1

theorem c3170 (w : Witness) : Before w false 6 8 → Before w false 8 17 → Before w false 17 6 → False :=
  fun z0 z1 z2 => cycle w false 6 8 17 z0 z1 z2

theorem c3185 (w : Witness) : Before w false 8 6 → Before w false 21 8 → Before w false 6 21 → False :=
  fun z0 z1 z2 => cycle w false 8 6 21 z0 z2 z1

theorem c3238 (w : Witness) : Before w false 6 10 → Before w false 10 11 → Before w false 11 6 → False :=
  fun z0 z1 z2 => cycle w false 6 10 11 z0 z1 z2

theorem c3243 (w : Witness) : Before w true 10 6 → Before w true 12 10 → Before w true 6 12 → False :=
  fun z0 z1 z2 => cycle w true 10 6 12 z0 z2 z1

theorem c3251 (w : Witness) : Before w true 10 6 → Before w true 14 10 → Before w true 6 14 → False :=
  fun z0 z1 z2 => cycle w true 10 6 14 z0 z2 z1

theorem c3277 (w : Witness) : Before w false 10 6 → Before w false 21 10 → Before w false 6 21 → False :=
  fun z0 z1 z2 => cycle w false 10 6 21 z0 z2 z1

theorem c3282 (w : Witness) : Before w false 6 11 → Before w false 11 12 → Before w false 12 6 → False :=
  fun z0 z1 z2 => cycle w false 6 11 12 z0 z1 z2

theorem c3293 (w : Witness) : Before w false 11 6 → Before w false 15 11 → Before w false 6 15 → False :=
  fun z0 z1 z2 => cycle w false 11 6 15 z0 z2 z1

theorem c3295 (w : Witness) : Before w true 11 6 → Before w true 15 11 → Before w true 6 15 → False :=
  fun z0 z1 z2 => cycle w true 11 6 15 z0 z2 z1

theorem c3325 (w : Witness) : Before w false 12 6 → Before w false 14 12 → Before w false 6 14 → False :=
  fun z0 z1 z2 => cycle w false 12 6 14 z0 z2 z1

theorem c3337 (w : Witness) : Before w false 12 6 → Before w false 17 12 → Before w false 6 17 → False :=
  fun z0 z1 z2 => cycle w false 12 6 17 z0 z2 z1

theorem c3351 (w : Witness) : Before w true 12 6 → Before w true 20 12 → Before w true 6 20 → False :=
  fun z0 z1 z2 => cycle w true 12 6 20 z0 z2 z1

theorem c3353 (w : Witness) : Before w false 12 6 → Before w false 21 12 → Before w false 6 21 → False :=
  fun z0 z1 z2 => cycle w false 12 6 21 z0 z2 z1

theorem c3355 (w : Witness) : Before w true 12 6 → Before w true 21 12 → Before w true 6 21 → False :=
  fun z0 z1 z2 => cycle w true 12 6 21 z0 z2 z1

theorem c3398 (w : Witness) : Before w false 6 14 → Before w false 14 17 → Before w false 17 6 → False :=
  fun z0 z1 z2 => cycle w false 6 14 17 z0 z1 z2

theorem c3399 (w : Witness) : Before w true 14 6 → Before w true 17 14 → Before w true 6 17 → False :=
  fun z0 z1 z2 => cycle w true 14 6 17 z0 z2 z1

theorem c3422 (w : Witness) : Before w false 6 15 → Before w false 15 17 → Before w false 17 6 → False :=
  fun z0 z1 z2 => cycle w false 6 15 17 z0 z1 z2

theorem c3430 (w : Witness) : Before w false 6 15 → Before w false 15 19 → Before w false 19 6 → False :=
  fun z0 z1 z2 => cycle w false 6 15 19 z0 z1 z2

theorem c3443 (w : Witness) : Before w true 16 6 → Before w true 17 16 → Before w true 6 17 → False :=
  fun z0 z1 z2 => cycle w true 16 6 17 z0 z2 z1

theorem c3447 (w : Witness) : Before w true 16 6 → Before w true 18 16 → Before w true 6 18 → False :=
  fun z0 z1 z2 => cycle w true 16 6 18 z0 z2 z1

theorem c3455 (w : Witness) : Before w true 16 6 → Before w true 20 16 → Before w true 6 20 → False :=
  fun z0 z1 z2 => cycle w true 16 6 20 z0 z2 z1

theorem c3463 (w : Witness) : Before w true 17 6 → Before w true 18 17 → Before w true 6 18 → False :=
  fun z0 z1 z2 => cycle w true 17 6 18 z0 z2 z1

theorem c3469 (w : Witness) : Before w false 17 6 → Before w false 20 17 → Before w false 6 20 → False :=
  fun z0 z1 z2 => cycle w false 17 6 20 z0 z2 z1

theorem c3471 (w : Witness) : Before w true 17 6 → Before w true 20 17 → Before w true 6 20 → False :=
  fun z0 z1 z2 => cycle w true 17 6 20 z0 z2 z1

theorem c3473 (w : Witness) : Before w false 17 6 → Before w false 21 17 → Before w false 6 21 → False :=
  fun z0 z1 z2 => cycle w false 17 6 21 z0 z2 z1

theorem c3475 (w : Witness) : Before w true 17 6 → Before w true 21 17 → Before w true 6 21 → False :=
  fun z0 z1 z2 => cycle w true 17 6 21 z0 z2 z1

theorem c3479 (w : Witness) : Before w true 18 6 → Before w true 19 18 → Before w true 6 19 → False :=
  fun z0 z1 z2 => cycle w true 18 6 19 z0 z2 z1

theorem c3481 (w : Witness) : Before w false 18 6 → Before w false 20 18 → Before w false 6 20 → False :=
  fun z0 z1 z2 => cycle w false 18 6 20 z0 z2 z1

theorem c3485 (w : Witness) : Before w false 18 6 → Before w false 21 18 → Before w false 6 21 → False :=
  fun z0 z1 z2 => cycle w false 18 6 21 z0 z2 z1

theorem c3495 (w : Witness) : Before w true 19 6 → Before w true 21 19 → Before w true 6 21 → False :=
  fun z0 z1 z2 => cycle w true 19 6 21 z0 z2 z1

theorem c3498 (w : Witness) : Before w false 6 20 → Before w false 20 21 → Before w false 21 6 → False :=
  fun z0 z1 z2 => cycle w false 6 20 21 z0 z1 z2

theorem c3499 (w : Witness) : Before w true 20 6 → Before w true 21 20 → Before w true 6 21 → False :=
  fun z0 z1 z2 => cycle w true 20 6 21 z0 z2 z1

theorem c3503 (w : Witness) : Before w true 8 7 → Before w true 9 8 → Before w true 7 9 → False :=
  fun z0 z1 z2 => cycle w true 8 7 9 z0 z2 z1

theorem c3514 (w : Witness) : Before w false 7 8 → Before w false 8 12 → Before w false 12 7 → False :=
  fun z0 z1 z2 => cycle w false 7 8 12 z0 z1 z2

theorem c3533 (w : Witness) : Before w false 8 7 → Before w false 17 8 → Before w false 7 17 → False :=
  fun z0 z1 z2 => cycle w false 8 7 17 z0 z2 z1

theorem c3539 (w : Witness) : Before w true 8 7 → Before w true 18 8 → Before w true 7 18 → False :=
  fun z0 z1 z2 => cycle w true 8 7 18 z0 z2 z1

theorem c3546 (w : Witness) : Before w false 7 8 → Before w false 8 20 → Before w false 20 7 → False :=
  fun z0 z1 z2 => cycle w false 7 8 20 z0 z1 z2

theorem c3550 (w : Witness) : Before w false 7 8 → Before w false 8 21 → Before w false 21 7 → False :=
  fun z0 z1 z2 => cycle w false 7 8 21 z0 z1 z2

theorem c3590 (w : Witness) : Before w false 7 9 → Before w false 9 19 → Before w false 19 7 → False :=
  fun z0 z1 z2 => cycle w false 7 9 19 z0 z1 z2

theorem c3595 (w : Witness) : Before w true 9 7 → Before w true 20 9 → Before w true 7 20 → False :=
  fun z0 z1 z2 => cycle w true 9 7 20 z0 z2 z1

theorem c3601 (w : Witness) : Before w false 10 7 → Before w false 11 10 → Before w false 7 11 → False :=
  fun z0 z1 z2 => cycle w false 10 7 11 z0 z2 z1

theorem c3603 (w : Witness) : Before w true 10 7 → Before w true 11 10 → Before w true 7 11 → False :=
  fun z0 z1 z2 => cycle w true 10 7 11 z0 z2 z1

theorem c3625 (w : Witness) : Before w false 10 7 → Before w false 17 10 → Before w false 7 17 → False :=
  fun z0 z1 z2 => cycle w false 10 7 17 z0 z2 z1

theorem c3629 (w : Witness) : Before w false 10 7 → Before w false 18 10 → Before w false 7 18 → False :=
  fun z0 z1 z2 => cycle w false 10 7 18 z0 z2 z1

theorem c3641 (w : Witness) : Before w false 10 7 → Before w false 21 10 → Before w false 7 21 → False :=
  fun z0 z1 z2 => cycle w false 10 7 21 z0 z2 z1

theorem c3647 (w : Witness) : Before w true 11 7 → Before w true 12 11 → Before w true 7 12 → False :=
  fun z0 z1 z2 => cycle w true 11 7 12 z0 z2 z1

theorem c3650 (w : Witness) : Before w false 7 11 → Before w false 11 13 → Before w false 13 7 → False :=
  fun z0 z1 z2 => cycle w false 7 11 13 z0 z1 z2

theorem c3651 (w : Witness) : Before w true 11 7 → Before w true 13 11 → Before w true 7 13 → False :=
  fun z0 z1 z2 => cycle w true 11 7 13 z0 z2 z1

theorem c3654 (w : Witness) : Before w false 7 11 → Before w false 11 14 → Before w false 14 7 → False :=
  fun z0 z1 z2 => cycle w false 7 11 14 z0 z1 z2

theorem c3666 (w : Witness) : Before w false 7 11 → Before w false 11 17 → Before w false 17 7 → False :=
  fun z0 z1 z2 => cycle w false 7 11 17 z0 z1 z2

theorem c3674 (w : Witness) : Before w false 7 11 → Before w false 11 19 → Before w false 19 7 → False :=
  fun z0 z1 z2 => cycle w false 7 11 19 z0 z1 z2

theorem c3682 (w : Witness) : Before w false 7 11 → Before w false 11 21 → Before w false 21 7 → False :=
  fun z0 z1 z2 => cycle w false 7 11 21 z0 z1 z2

theorem c3686 (w : Witness) : Before w false 7 12 → Before w false 12 13 → Before w false 13 7 → False :=
  fun z0 z1 z2 => cycle w false 7 12 13 z0 z1 z2

theorem c3707 (w : Witness) : Before w true 12 7 → Before w true 18 12 → Before w true 7 18 → False :=
  fun z0 z1 z2 => cycle w true 12 7 18 z0 z2 z1

theorem c3715 (w : Witness) : Before w true 12 7 → Before w true 20 12 → Before w true 7 20 → False :=
  fun z0 z1 z2 => cycle w true 12 7 20 z0 z2 z1

theorem c3733 (w : Witness) : Before w false 13 7 → Before w false 17 13 → Before w false 7 17 → False :=
  fun z0 z1 z2 => cycle w false 13 7 17 z0 z2 z1

theorem c3738 (w : Witness) : Before w false 7 13 → Before w false 13 18 → Before w false 18 7 → False :=
  fun z0 z1 z2 => cycle w false 7 13 18 z0 z1 z2

theorem c3739 (w : Witness) : Before w true 13 7 → Before w true 18 13 → Before w true 7 18 → False :=
  fun z0 z1 z2 => cycle w true 13 7 18 z0 z2 z1

theorem c3742 (w : Witness) : Before w false 7 13 → Before w false 13 19 → Before w false 19 7 → False :=
  fun z0 z1 z2 => cycle w false 7 13 19 z0 z1 z2

theorem c3775 (w : Witness) : Before w true 14 7 → Before w true 20 14 → Before w true 7 20 → False :=
  fun z0 z1 z2 => cycle w true 14 7 20 z0 z2 z1

theorem c3790 (w : Witness) : Before w false 7 15 → Before w false 15 18 → Before w false 18 7 → False :=
  fun z0 z1 z2 => cycle w false 7 15 18 z0 z1 z2

theorem c3794 (w : Witness) : Before w false 7 15 → Before w false 15 19 → Before w false 19 7 → False :=
  fun z0 z1 z2 => cycle w false 7 15 19 z0 z1 z2

theorem c3799 (w : Witness) : Before w true 15 7 → Before w true 20 15 → Before w true 7 20 → False :=
  fun z0 z1 z2 => cycle w true 15 7 20 z0 z2 z1

theorem c3822 (w : Witness) : Before w false 7 16 → Before w false 16 21 → Before w false 21 7 → False :=
  fun z0 z1 z2 => cycle w false 7 16 21 z0 z1 z2

theorem c3826 (w : Witness) : Before w false 7 17 → Before w false 17 18 → Before w false 18 7 → False :=
  fun z0 z1 z2 => cycle w false 7 17 18 z0 z1 z2

theorem c3831 (w : Witness) : Before w true 17 7 → Before w true 19 17 → Before w true 7 19 → False :=
  fun z0 z1 z2 => cycle w true 17 7 19 z0 z2 z1

theorem c3838 (w : Witness) : Before w false 7 17 → Before w false 17 21 → Before w false 21 7 → False :=
  fun z0 z1 z2 => cycle w false 7 17 21 z0 z1 z2

theorem c3839 (w : Witness) : Before w true 17 7 → Before w true 21 17 → Before w true 7 21 → False :=
  fun z0 z1 z2 => cycle w true 17 7 21 z0 z2 z1

theorem c3843 (w : Witness) : Before w true 18 7 → Before w true 19 18 → Before w true 7 19 → False :=
  fun z0 z1 z2 => cycle w true 18 7 19 z0 z2 z1

theorem c3847 (w : Witness) : Before w true 18 7 → Before w true 20 18 → Before w true 7 20 → False :=
  fun z0 z1 z2 => cycle w true 18 7 20 z0 z2 z1

theorem c3875 (w : Witness) : Before w true 9 8 → Before w true 12 9 → Before w true 8 12 → False :=
  fun z0 z1 z2 => cycle w true 9 8 12 z0 z2 z1

theorem c3895 (w : Witness) : Before w true 9 8 → Before w true 17 9 → Before w true 8 17 → False :=
  fun z0 z1 z2 => cycle w true 9 8 17 z0 z2 z1

theorem c3898 (w : Witness) : Before w false 8 9 → Before w false 9 18 → Before w false 18 8 → False :=
  fun z0 z1 z2 => cycle w false 8 9 18 z0 z1 z2

theorem c3914 (w : Witness) : Before w false 8 10 → Before w false 10 11 → Before w false 11 8 → False :=
  fun z0 z1 z2 => cycle w false 8 10 11 z0 z1 z2

theorem c3915 (w : Witness) : Before w true 10 8 → Before w true 11 10 → Before w true 8 11 → False :=
  fun z0 z1 z2 => cycle w true 10 8 11 z0 z2 z1

theorem c3919 (w : Witness) : Before w true 10 8 → Before w true 12 10 → Before w true 8 12 → False :=
  fun z0 z1 z2 => cycle w true 10 8 12 z0 z2 z1

theorem c3931 (w : Witness) : Before w true 10 8 → Before w true 15 10 → Before w true 8 15 → False :=
  fun z0 z1 z2 => cycle w true 10 8 15 z0 z2 z1

theorem c3938 (w : Witness) : Before w false 8 10 → Before w false 10 17 → Before w false 17 8 → False :=
  fun z0 z1 z2 => cycle w false 8 10 17 z0 z1 z2

theorem c3946 (w : Witness) : Before w false 8 10 → Before w false 10 19 → Before w false 19 8 → False :=
  fun z0 z1 z2 => cycle w false 8 10 19 z0 z1 z2

theorem c3949 (w : Witness) : Before w false 10 8 → Before w false 20 10 → Before w false 8 20 → False :=
  fun z0 z1 z2 => cycle w false 10 8 20 z0 z2 z1

theorem c3953 (w : Witness) : Before w false 10 8 → Before w false 21 10 → Before w false 8 21 → False :=
  fun z0 z1 z2 => cycle w false 10 8 21 z0 z2 z1

theorem c3957 (w : Witness) : Before w false 11 8 → Before w false 12 11 → Before w false 8 12 → False :=
  fun z0 z1 z2 => cycle w false 11 8 12 z0 z2 z1

theorem c3978 (w : Witness) : Before w false 8 11 → Before w false 11 17 → Before w false 17 8 → False :=
  fun z0 z1 z2 => cycle w false 8 11 17 z0 z1 z2

theorem c3983 (w : Witness) : Before w true 11 8 → Before w true 18 11 → Before w true 8 18 → False :=
  fun z0 z1 z2 => cycle w true 11 8 18 z0 z2 z1

theorem c3985 (w : Witness) : Before w false 11 8 → Before w false 19 11 → Before w false 8 19 → False :=
  fun z0 z1 z2 => cycle w false 11 8 19 z0 z2 z1

theorem c3993 (w : Witness) : Before w false 11 8 → Before w false 21 11 → Before w false 8 21 → False :=
  fun z0 z1 z2 => cycle w false 11 8 21 z0 z2 z1

theorem c3999 (w : Witness) : Before w true 12 8 → Before w true 13 12 → Before w true 8 13 → False :=
  fun z0 z1 z2 => cycle w true 12 8 13 z0 z2 z1

theorem c4011 (w : Witness) : Before w true 12 8 → Before w true 16 12 → Before w true 8 16 → False :=
  fun z0 z1 z2 => cycle w true 12 8 16 z0 z2 z1

theorem c4014 (w : Witness) : Before w false 8 12 → Before w false 12 17 → Before w false 17 8 → False :=
  fun z0 z1 z2 => cycle w false 8 12 17 z0 z1 z2

theorem c4015 (w : Witness) : Before w true 12 8 → Before w true 17 12 → Before w true 8 17 → False :=
  fun z0 z1 z2 => cycle w true 12 8 17 z0 z2 z1

theorem c4019 (w : Witness) : Before w true 12 8 → Before w true 18 12 → Before w true 8 18 → False :=
  fun z0 z1 z2 => cycle w true 12 8 18 z0 z2 z1

theorem c4022 (w : Witness) : Before w false 8 12 → Before w false 12 19 → Before w false 19 8 → False :=
  fun z0 z1 z2 => cycle w false 8 12 19 z0 z1 z2

theorem c4030 (w : Witness) : Before w false 8 12 → Before w false 12 21 → Before w false 21 8 → False :=
  fun z0 z1 z2 => cycle w false 8 12 21 z0 z1 z2

theorem c4043 (w : Witness) : Before w true 13 8 → Before w true 16 13 → Before w true 8 16 → False :=
  fun z0 z1 z2 => cycle w true 13 8 16 z0 z2 z1

theorem c4047 (w : Witness) : Before w true 13 8 → Before w true 17 13 → Before w true 8 17 → False :=
  fun z0 z1 z2 => cycle w true 13 8 17 z0 z2 z1

theorem c4055 (w : Witness) : Before w true 13 8 → Before w true 19 13 → Before w true 8 19 → False :=
  fun z0 z1 z2 => cycle w true 13 8 19 z0 z2 z1

theorem c4059 (w : Witness) : Before w true 13 8 → Before w true 20 13 → Before w true 8 20 → False :=
  fun z0 z1 z2 => cycle w true 13 8 20 z0 z2 z1

theorem c4079 (w : Witness) : Before w true 14 8 → Before w true 18 14 → Before w true 8 18 → False :=
  fun z0 z1 z2 => cycle w true 14 8 18 z0 z2 z1

theorem c4082 (w : Witness) : Before w false 8 14 → Before w false 14 19 → Before w false 19 8 → False :=
  fun z0 z1 z2 => cycle w false 8 14 19 z0 z1 z2

theorem c4085 (w : Witness) : Before w false 14 8 → Before w false 20 14 → Before w false 8 20 → False :=
  fun z0 z1 z2 => cycle w false 14 8 20 z0 z2 z1

theorem c4089 (w : Witness) : Before w false 14 8 → Before w false 21 14 → Before w false 8 21 → False :=
  fun z0 z1 z2 => cycle w false 14 8 21 z0 z2 z1

theorem c4095 (w : Witness) : Before w true 15 8 → Before w true 16 15 → Before w true 8 16 → False :=
  fun z0 z1 z2 => cycle w true 15 8 16 z0 z2 z1

theorem c4098 (w : Witness) : Before w false 8 15 → Before w false 15 17 → Before w false 17 8 → False :=
  fun z0 z1 z2 => cycle w false 8 15 17 z0 z1 z2

theorem c4102 (w : Witness) : Before w false 8 15 → Before w false 15 18 → Before w false 18 8 → False :=
  fun z0 z1 z2 => cycle w false 8 15 18 z0 z1 z2

theorem c4119 (w : Witness) : Before w true 16 8 → Before w true 17 16 → Before w true 8 17 → False :=
  fun z0 z1 z2 => cycle w true 16 8 17 z0 z2 z1

theorem c4123 (w : Witness) : Before w true 16 8 → Before w true 18 16 → Before w true 8 18 → False :=
  fun z0 z1 z2 => cycle w true 16 8 18 z0 z2 z1

theorem c4141 (w : Witness) : Before w false 17 8 → Before w false 19 17 → Before w false 8 19 → False :=
  fun z0 z1 z2 => cycle w false 17 8 19 z0 z2 z1

theorem c4145 (w : Witness) : Before w false 17 8 → Before w false 20 17 → Before w false 8 20 → False :=
  fun z0 z1 z2 => cycle w false 17 8 20 z0 z2 z1

theorem c4147 (w : Witness) : Before w true 17 8 → Before w true 20 17 → Before w true 8 20 → False :=
  fun z0 z1 z2 => cycle w true 17 8 20 z0 z2 z1

theorem c4149 (w : Witness) : Before w false 17 8 → Before w false 21 17 → Before w false 8 21 → False :=
  fun z0 z1 z2 => cycle w false 17 8 21 z0 z2 z1

theorem c4154 (w : Witness) : Before w false 8 18 → Before w false 18 19 → Before w false 19 8 → False :=
  fun z0 z1 z2 => cycle w false 8 18 19 z0 z1 z2

theorem c4159 (w : Witness) : Before w true 18 8 → Before w true 20 18 → Before w true 8 20 → False :=
  fun z0 z1 z2 => cycle w true 18 8 20 z0 z2 z1

theorem c4165 (w : Witness) : Before w false 19 8 → Before w false 20 19 → Before w false 8 20 → False :=
  fun z0 z1 z2 => cycle w false 19 8 20 z0 z2 z1

theorem c4167 (w : Witness) : Before w true 19 8 → Before w true 20 19 → Before w true 8 20 → False :=
  fun z0 z1 z2 => cycle w true 19 8 20 z0 z2 z1

theorem c4169 (w : Witness) : Before w false 19 8 → Before w false 21 19 → Before w false 8 21 → False :=
  fun z0 z1 z2 => cycle w false 19 8 21 z0 z2 z1

theorem c4171 (w : Witness) : Before w true 19 8 → Before w true 21 19 → Before w true 8 21 → False :=
  fun z0 z1 z2 => cycle w true 19 8 21 z0 z2 z1

theorem c4175 (w : Witness) : Before w true 20 8 → Before w true 21 20 → Before w true 8 21 → False :=
  fun z0 z1 z2 => cycle w true 20 8 21 z0 z2 z1

theorem c4182 (w : Witness) : Before w false 9 10 → Before w false 10 12 → Before w false 12 9 → False :=
  fun z0 z1 z2 => cycle w false 9 10 12 z0 z1 z2

theorem c4185 (w : Witness) : Before w false 10 9 → Before w false 13 10 → Before w false 9 13 → False :=
  fun z0 z1 z2 => cycle w false 10 9 13 z0 z2 z1

theorem c4190 (w : Witness) : Before w false 9 10 → Before w false 10 14 → Before w false 14 9 → False :=
  fun z0 z1 z2 => cycle w false 9 10 14 z0 z1 z2

theorem c4217 (w : Witness) : Before w false 10 9 → Before w false 21 10 → Before w false 9 21 → False :=
  fun z0 z1 z2 => cycle w false 10 9 21 z0 z2 z1

theorem c4222 (w : Witness) : Before w false 9 11 → Before w false 11 12 → Before w false 12 9 → False :=
  fun z0 z1 z2 => cycle w false 9 11 12 z0 z1 z2

theorem c4227 (w : Witness) : Before w true 11 9 → Before w true 13 11 → Before w true 9 13 → False :=
  fun z0 z1 z2 => cycle w true 11 9 13 z0 z2 z1

theorem c4229 (w : Witness) : Before w false 11 9 → Before w false 14 11 → Before w false 9 14 → False :=
  fun z0 z1 z2 => cycle w false 11 9 14 z0 z2 z1

theorem c4257 (w : Witness) : Before w false 11 9 → Before w false 21 11 → Before w false 9 21 → False :=
  fun z0 z1 z2 => cycle w false 11 9 21 z0 z2 z1

theorem c4265 (w : Witness) : Before w false 12 9 → Before w false 14 12 → Before w false 9 14 → False :=
  fun z0 z1 z2 => cycle w false 12 9 14 z0 z2 z1

theorem c4293 (w : Witness) : Before w false 12 9 → Before w false 21 12 → Before w false 9 21 → False :=
  fun z0 z1 z2 => cycle w false 12 9 21 z0 z2 z1

theorem c4299 (w : Witness) : Before w true 13 9 → Before w true 14 13 → Before w true 9 14 → False :=
  fun z0 z1 z2 => cycle w true 13 9 14 z0 z2 z1

theorem c4303 (w : Witness) : Before w true 13 9 → Before w true 15 13 → Before w true 9 15 → False :=
  fun z0 z1 z2 => cycle w true 13 9 15 z0 z2 z1

theorem c4305 (w : Witness) : Before w false 13 9 → Before w false 16 13 → Before w false 9 16 → False :=
  fun z0 z1 z2 => cycle w false 13 9 16 z0 z2 z1

theorem c4331 (w : Witness) : Before w true 14 9 → Before w true 15 14 → Before w true 9 15 → False :=
  fun z0 z1 z2 => cycle w true 14 9 15 z0 z2 z1

theorem c4346 (w : Witness) : Before w false 9 14 → Before w false 14 19 → Before w false 19 9 → False :=
  fun z0 z1 z2 => cycle w false 9 14 19 z0 z1 z2

theorem c4351 (w : Witness) : Before w true 14 9 → Before w true 20 14 → Before w true 9 20 → False :=
  fun z0 z1 z2 => cycle w true 14 9 20 z0 z2 z1

theorem c4387 (w : Witness) : Before w true 16 9 → Before w true 18 16 → Before w true 9 18 → False :=
  fun z0 z1 z2 => cycle w true 16 9 18 z0 z2 z1

theorem c4418 (w : Witness) : Before w false 9 18 → Before w false 18 19 → Before w false 19 9 → False :=
  fun z0 z1 z2 => cycle w false 9 18 19 z0 z1 z2

theorem c4442 (w : Witness) : Before w false 10 11 → Before w false 11 12 → Before w false 12 10 → False :=
  fun z0 z1 z2 => cycle w false 10 11 12 z0 z1 z2

theorem c4443 (w : Witness) : Before w true 11 10 → Before w true 12 11 → Before w true 10 12 → False :=
  fun z0 z1 z2 => cycle w true 11 10 12 z0 z2 z1

theorem c4449 (w : Witness) : Before w false 11 10 → Before w false 14 11 → Before w false 10 14 → False :=
  fun z0 z1 z2 => cycle w false 11 10 14 z0 z2 z1

theorem c4471 (w : Witness) : Before w true 11 10 → Before w true 19 11 → Before w true 10 19 → False :=
  fun z0 z1 z2 => cycle w true 11 10 19 z0 z2 z1

theorem c4474 (w : Witness) : Before w false 10 11 → Before w false 11 20 → Before w false 20 10 → False :=
  fun z0 z1 z2 => cycle w false 10 11 20 z0 z1 z2

theorem c4483 (w : Witness) : Before w true 12 10 → Before w true 13 12 → Before w true 10 13 → False :=
  fun z0 z1 z2 => cycle w true 12 10 13 z0 z2 z1

theorem c4503 (w : Witness) : Before w true 12 10 → Before w true 18 12 → Before w true 10 18 → False :=
  fun z0 z1 z2 => cycle w true 12 10 18 z0 z2 z1

theorem c4507 (w : Witness) : Before w true 12 10 → Before w true 19 12 → Before w true 10 19 → False :=
  fun z0 z1 z2 => cycle w true 12 10 19 z0 z2 z1

theorem c4514 (w : Witness) : Before w false 10 12 → Before w false 12 21 → Before w false 21 10 → False :=
  fun z0 z1 z2 => cycle w false 10 12 21 z0 z1 z2

theorem c4515 (w : Witness) : Before w true 12 10 → Before w true 21 12 → Before w true 10 21 → False :=
  fun z0 z1 z2 => cycle w true 12 10 21 z0 z2 z1

theorem c4525 (w : Witness) : Before w false 13 10 → Before w false 16 13 → Before w false 10 16 → False :=
  fun z0 z1 z2 => cycle w false 13 10 16 z0 z2 z1

theorem c4534 (w : Witness) : Before w false 10 13 → Before w false 13 18 → Before w false 18 10 → False :=
  fun z0 z1 z2 => cycle w false 10 13 18 z0 z1 z2

theorem c4537 (w : Witness) : Before w false 13 10 → Before w false 19 13 → Before w false 10 19 → False :=
  fun z0 z1 z2 => cycle w false 13 10 19 z0 z2 z1

theorem c4544 (w : Witness) : Before w true 10 13 → Before w true 13 20 → Before w true 20 10 → False :=
  fun z0 z1 z2 => cycle w true 10 13 20 z0 z1 z2

theorem c4550 (w : Witness) : Before w false 10 14 → Before w false 14 15 → Before w false 15 10 → False :=
  fun z0 z1 z2 => cycle w false 10 14 15 z0 z1 z2

theorem c4562 (w : Witness) : Before w false 10 14 → Before w false 14 18 → Before w false 18 10 → False :=
  fun z0 z1 z2 => cycle w false 10 14 18 z0 z1 z2

theorem c4563 (w : Witness) : Before w true 14 10 → Before w true 18 14 → Before w true 10 18 → False :=
  fun z0 z1 z2 => cycle w true 14 10 18 z0 z2 z1

theorem c4566 (w : Witness) : Before w false 10 14 → Before w false 14 19 → Before w false 19 10 → False :=
  fun z0 z1 z2 => cycle w false 10 14 19 z0 z1 z2

theorem c4574 (w : Witness) : Before w false 10 14 → Before w false 14 21 → Before w false 21 10 → False :=
  fun z0 z1 z2 => cycle w false 10 14 21 z0 z1 z2

theorem c4586 (w : Witness) : Before w false 10 15 → Before w false 15 18 → Before w false 18 10 → False :=
  fun z0 z1 z2 => cycle w false 10 15 18 z0 z1 z2

theorem c4606 (w : Witness) : Before w false 10 16 → Before w false 16 18 → Before w false 18 10 → False :=
  fun z0 z1 z2 => cycle w false 10 16 18 z0 z1 z2

theorem c4609 (w : Witness) : Before w false 16 10 → Before w false 19 16 → Before w false 10 19 → False :=
  fun z0 z1 z2 => cycle w false 16 10 19 z0 z2 z1

theorem c4611 (w : Witness) : Before w true 16 10 → Before w true 19 16 → Before w true 10 19 → False :=
  fun z0 z1 z2 => cycle w true 16 10 19 z0 z2 z1

theorem c4615 (w : Witness) : Before w true 16 10 → Before w true 20 16 → Before w true 10 20 → False :=
  fun z0 z1 z2 => cycle w true 16 10 20 z0 z2 z1

theorem c4625 (w : Witness) : Before w false 17 10 → Before w false 19 17 → Before w false 10 19 → False :=
  fun z0 z1 z2 => cycle w false 17 10 19 z0 z2 z1

theorem c4630 (w : Witness) : Before w false 10 17 → Before w false 17 20 → Before w false 20 10 → False :=
  fun z0 z1 z2 => cycle w false 10 17 20 z0 z1 z2

theorem c4637 (w : Witness) : Before w false 18 10 → Before w false 19 18 → Before w false 10 19 → False :=
  fun z0 z1 z2 => cycle w false 18 10 19 z0 z2 z1

theorem c4639 (w : Witness) : Before w true 18 10 → Before w true 19 18 → Before w true 10 19 → False :=
  fun z0 z1 z2 => cycle w true 18 10 19 z0 z2 z1

theorem c4650 (w : Witness) : Before w false 10 19 → Before w false 19 20 → Before w false 20 10 → False :=
  fun z0 z1 z2 => cycle w false 10 19 20 z0 z1 z2

theorem c4654 (w : Witness) : Before w false 10 19 → Before w false 19 21 → Before w false 21 10 → False :=
  fun z0 z1 z2 => cycle w false 10 19 21 z0 z1 z2

theorem c4655 (w : Witness) : Before w true 19 10 → Before w true 21 19 → Before w true 10 21 → False :=
  fun z0 z1 z2 => cycle w true 19 10 21 z0 z2 z1

theorem c4659 (w : Witness) : Before w true 20 10 → Before w true 21 20 → Before w true 10 21 → False :=
  fun z0 z1 z2 => cycle w true 20 10 21 z0 z2 z1

theorem c4666 (w : Witness) : Before w false 11 12 → Before w false 12 14 → Before w false 14 11 → False :=
  fun z0 z1 z2 => cycle w false 11 12 14 z0 z1 z2

theorem c4667 (w : Witness) : Before w true 12 11 → Before w true 14 12 → Before w true 11 14 → False :=
  fun z0 z1 z2 => cycle w true 12 11 14 z0 z2 z1

theorem c4685 (w : Witness) : Before w false 12 11 → Before w false 19 12 → Before w false 11 19 → False :=
  fun z0 z1 z2 => cycle w false 12 11 19 z0 z2 z1

theorem c4690 (w : Witness) : Before w false 11 12 → Before w false 12 20 → Before w false 20 11 → False :=
  fun z0 z1 z2 => cycle w false 11 12 20 z0 z1 z2

theorem c4714 (w : Witness) : Before w false 11 13 → Before w false 13 18 → Before w false 18 11 → False :=
  fun z0 z1 z2 => cycle w false 11 13 18 z0 z1 z2

theorem c4715 (w : Witness) : Before w true 13 11 → Before w true 18 13 → Before w true 11 18 → False :=
  fun z0 z1 z2 => cycle w true 13 11 18 z0 z2 z1

theorem c4729 (w : Witness) : Before w false 14 11 → Before w false 15 14 → Before w false 11 15 → False :=
  fun z0 z1 z2 => cycle w false 14 11 15 z0 z2 z1

theorem c4735 (w : Witness) : Before w true 14 11 → Before w true 16 14 → Before w true 11 16 → False :=
  fun z0 z1 z2 => cycle w true 14 11 16 z0 z2 z1

theorem c4753 (w : Witness) : Before w false 14 11 → Before w false 21 14 → Before w false 11 21 → False :=
  fun z0 z1 z2 => cycle w false 14 11 21 z0 z2 z1

theorem c4778 (w : Witness) : Before w false 11 15 → Before w false 15 21 → Before w false 21 11 → False :=
  fun z0 z1 z2 => cycle w false 11 15 21 z0 z1 z2

theorem c4781 (w : Witness) : Before w false 16 11 → Before w false 17 16 → Before w false 11 17 → False :=
  fun z0 z1 z2 => cycle w false 16 11 17 z0 z2 z1

theorem c4798 (w : Witness) : Before w false 11 16 → Before w false 16 21 → Before w false 21 11 → False :=
  fun z0 z1 z2 => cycle w false 11 16 21 z0 z1 z2

theorem c4810 (w : Witness) : Before w false 11 17 → Before w false 17 20 → Before w false 20 11 → False :=
  fun z0 z1 z2 => cycle w false 11 17 20 z0 z1 z2

theorem c4814 (w : Witness) : Before w false 11 17 → Before w false 17 21 → Before w false 21 11 → False :=
  fun z0 z1 z2 => cycle w false 11 17 21 z0 z1 z2

theorem c4815 (w : Witness) : Before w true 17 11 → Before w true 21 17 → Before w true 11 21 → False :=
  fun z0 z1 z2 => cycle w true 17 11 21 z0 z2 z1

theorem c4833 (w : Witness) : Before w false 19 11 → Before w false 21 19 → Before w false 11 21 → False :=
  fun z0 z1 z2 => cycle w false 19 11 21 z0 z2 z1

theorem c4835 (w : Witness) : Before w true 19 11 → Before w true 21 19 → Before w true 11 21 → False :=
  fun z0 z1 z2 => cycle w true 19 11 21 z0 z2 z1

theorem c4838 (w : Witness) : Before w false 11 20 → Before w false 20 21 → Before w false 21 11 → False :=
  fun z0 z1 z2 => cycle w false 11 20 21 z0 z1 z2

theorem c4862 (w : Witness) : Before w false 12 13 → Before w false 13 19 → Before w false 19 12 → False :=
  fun z0 z1 z2 => cycle w false 12 13 19 z0 z1 z2

theorem c4863 (w : Witness) : Before w true 13 12 → Before w true 19 13 → Before w true 12 19 → False :=
  fun z0 z1 z2 => cycle w true 13 12 19 z0 z2 z1

theorem c4867 (w : Witness) : Before w true 13 12 → Before w true 20 13 → Before w true 12 20 → False :=
  fun z0 z1 z2 => cycle w true 13 12 20 z0 z2 z1

theorem c4869 (w : Witness) : Before w false 13 12 → Before w false 21 13 → Before w false 12 21 → False :=
  fun z0 z1 z2 => cycle w false 13 12 21 z0 z2 z1

theorem c4883 (w : Witness) : Before w true 14 12 → Before w true 17 14 → Before w true 12 17 → False :=
  fun z0 z1 z2 => cycle w true 14 12 17 z0 z2 z1

theorem c4893 (w : Witness) : Before w false 14 12 → Before w false 20 14 → Before w false 12 20 → False :=
  fun z0 z1 z2 => cycle w false 14 12 20 z0 z2 z1

theorem c4897 (w : Witness) : Before w false 14 12 → Before w false 21 14 → Before w false 12 21 → False :=
  fun z0 z1 z2 => cycle w false 14 12 21 z0 z2 z1

theorem c4907 (w : Witness) : Before w true 15 12 → Before w true 17 15 → Before w true 12 17 → False :=
  fun z0 z1 z2 => cycle w true 15 12 17 z0 z2 z1

theorem c4911 (w : Witness) : Before w true 15 12 → Before w true 18 15 → Before w true 12 18 → False :=
  fun z0 z1 z2 => cycle w true 15 12 18 z0 z2 z1

theorem c4927 (w : Witness) : Before w true 16 12 → Before w true 17 16 → Before w true 12 17 → False :=
  fun z0 z1 z2 => cycle w true 16 12 17 z0 z2 z1

theorem c4935 (w : Witness) : Before w true 16 12 → Before w true 19 16 → Before w true 12 19 → False :=
  fun z0 z1 z2 => cycle w true 16 12 19 z0 z2 z1

theorem c4939 (w : Witness) : Before w true 16 12 → Before w true 20 16 → Before w true 12 20 → False :=
  fun z0 z1 z2 => cycle w true 16 12 20 z0 z2 z1

theorem c4945 (w : Witness) : Before w false 17 12 → Before w false 18 17 → Before w false 12 18 → False :=
  fun z0 z1 z2 => cycle w false 17 12 18 z0 z2 z1

theorem c4947 (w : Witness) : Before w true 17 12 → Before w true 18 17 → Before w true 12 18 → False :=
  fun z0 z1 z2 => cycle w true 17 12 18 z0 z2 z1

theorem c4951 (w : Witness) : Before w true 17 12 → Before w true 19 17 → Before w true 12 19 → False :=
  fun z0 z1 z2 => cycle w true 17 12 19 z0 z2 z1

theorem c4953 (w : Witness) : Before w false 17 12 → Before w false 20 17 → Before w false 12 20 → False :=
  fun z0 z1 z2 => cycle w false 17 12 20 z0 z2 z1

theorem c4955 (w : Witness) : Before w true 17 12 → Before w true 20 17 → Before w true 12 20 → False :=
  fun z0 z1 z2 => cycle w true 17 12 20 z0 z2 z1

theorem c4957 (w : Witness) : Before w false 17 12 → Before w false 21 17 → Before w false 12 21 → False :=
  fun z0 z1 z2 => cycle w false 17 12 21 z0 z2 z1

theorem c4962 (w : Witness) : Before w false 12 18 → Before w false 18 19 → Before w false 19 12 → False :=
  fun z0 z1 z2 => cycle w false 12 18 19 z0 z1 z2

theorem c4963 (w : Witness) : Before w true 18 12 → Before w true 19 18 → Before w true 12 19 → False :=
  fun z0 z1 z2 => cycle w true 18 12 19 z0 z2 z1

theorem c4969 (w : Witness) : Before w false 18 12 → Before w false 21 18 → Before w false 12 21 → False :=
  fun z0 z1 z2 => cycle w false 18 12 21 z0 z2 z1

theorem c4971 (w : Witness) : Before w true 18 12 → Before w true 21 18 → Before w true 12 21 → False :=
  fun z0 z1 z2 => cycle w true 18 12 21 z0 z2 z1

theorem c4973 (w : Witness) : Before w false 19 12 → Before w false 20 19 → Before w false 12 20 → False :=
  fun z0 z1 z2 => cycle w false 19 12 20 z0 z2 z1

theorem c4975 (w : Witness) : Before w true 19 12 → Before w true 20 19 → Before w true 12 20 → False :=
  fun z0 z1 z2 => cycle w true 19 12 20 z0 z2 z1

theorem c4983 (w : Witness) : Before w true 20 12 → Before w true 21 20 → Before w true 12 21 → False :=
  fun z0 z1 z2 => cycle w true 20 12 21 z0 z2 z1

theorem c4990 (w : Witness) : Before w false 13 14 → Before w false 14 16 → Before w false 16 13 → False :=
  fun z0 z1 z2 => cycle w false 13 14 16 z0 z1 z2

theorem c4997 (w : Witness) : Before w false 14 13 → Before w false 18 14 → Before w false 13 18 → False :=
  fun z0 z1 z2 => cycle w false 14 13 18 z0 z2 z1

theorem c5002 (w : Witness) : Before w false 13 14 → Before w false 14 19 → Before w false 19 13 → False :=
  fun z0 z1 z2 => cycle w false 13 14 19 z0 z1 z2

theorem c5011 (w : Witness) : Before w true 14 13 → Before w true 21 14 → Before w true 13 21 → False :=
  fun z0 z1 z2 => cycle w true 14 13 21 z0 z2 z1

theorem c5019 (w : Witness) : Before w true 15 13 → Before w true 17 15 → Before w true 13 17 → False :=
  fun z0 z1 z2 => cycle w true 15 13 17 z0 z2 z1

theorem c5041 (w : Witness) : Before w false 16 13 → Before w false 18 16 → Before w false 13 18 → False :=
  fun z0 z1 z2 => cycle w false 16 13 18 z0 z2 z1

theorem c5047 (w : Witness) : Before w true 16 13 → Before w true 19 16 → Before w true 13 19 → False :=
  fun z0 z1 z2 => cycle w true 16 13 19 z0 z2 z1

theorem c5051 (w : Witness) : Before w true 16 13 → Before w true 20 16 → Before w true 13 20 → False :=
  fun z0 z1 z2 => cycle w true 16 13 20 z0 z2 z1

theorem c5061 (w : Witness) : Before w false 17 13 → Before w false 19 17 → Before w false 13 19 → False :=
  fun z0 z1 z2 => cycle w false 17 13 19 z0 z2 z1

theorem c5063 (w : Witness) : Before w true 17 13 → Before w true 19 17 → Before w true 13 19 → False :=
  fun z0 z1 z2 => cycle w true 17 13 19 z0 z2 z1

theorem c5074 (w : Witness) : Before w false 13 18 → Before w false 18 19 → Before w false 19 13 → False :=
  fun z0 z1 z2 => cycle w false 13 18 19 z0 z1 z2

theorem c5078 (w : Witness) : Before w false 13 18 → Before w false 18 20 → Before w false 20 13 → False :=
  fun z0 z1 z2 => cycle w false 13 18 20 z0 z1 z2

theorem c5086 (w : Witness) : Before w false 13 19 → Before w false 19 20 → Before w false 20 13 → False :=
  fun z0 z1 z2 => cycle w false 13 19 20 z0 z1 z2

theorem c5094 (w : Witness) : Before w false 13 20 → Before w false 20 21 → Before w false 21 13 → False :=
  fun z0 z1 z2 => cycle w false 13 20 21 z0 z1 z2

theorem c5103 (w : Witness) : Before w true 15 14 → Before w true 17 15 → Before w true 14 17 → False :=
  fun z0 z1 z2 => cycle w true 15 14 17 z0 z2 z1

theorem c5123 (w : Witness) : Before w true 16 14 → Before w true 17 16 → Before w true 14 17 → False :=
  fun z0 z1 z2 => cycle w true 16 14 17 z0 z2 z1

theorem c5129 (w : Witness) : Before w false 16 14 → Before w false 19 16 → Before w false 14 19 → False :=
  fun z0 z1 z2 => cycle w false 16 14 19 z0 z2 z1

theorem c5135 (w : Witness) : Before w true 16 14 → Before w true 20 16 → Before w true 14 20 → False :=
  fun z0 z1 z2 => cycle w true 16 14 20 z0 z2 z1

theorem c5151 (w : Witness) : Before w true 17 14 → Before w true 20 17 → Before w true 14 20 → False :=
  fun z0 z1 z2 => cycle w true 17 14 20 z0 z2 z1

theorem c5159 (w : Witness) : Before w true 18 14 → Before w true 19 18 → Before w true 14 19 → False :=
  fun z0 z1 z2 => cycle w true 18 14 19 z0 z2 z1

theorem c5163 (w : Witness) : Before w true 18 14 → Before w true 20 18 → Before w true 14 20 → False :=
  fun z0 z1 z2 => cycle w true 18 14 20 z0 z2 z1

theorem c5165 (w : Witness) : Before w false 18 14 → Before w false 21 18 → Before w false 14 21 → False :=
  fun z0 z1 z2 => cycle w false 18 14 21 z0 z2 z1

theorem c5170 (w : Witness) : Before w false 14 19 → Before w false 19 20 → Before w false 20 14 → False :=
  fun z0 z1 z2 => cycle w false 14 19 20 z0 z1 z2

theorem c5171 (w : Witness) : Before w true 19 14 → Before w true 20 19 → Before w true 14 20 → False :=
  fun z0 z1 z2 => cycle w true 19 14 20 z0 z2 z1

theorem c5174 (w : Witness) : Before w false 14 19 → Before w false 19 21 → Before w false 21 14 → False :=
  fun z0 z1 z2 => cycle w false 14 19 21 z0 z1 z2

theorem c5175 (w : Witness) : Before w true 19 14 → Before w true 21 19 → Before w true 14 21 → False :=
  fun z0 z1 z2 => cycle w true 19 14 21 z0 z2 z1

theorem c5183 (w : Witness) : Before w true 16 15 → Before w true 17 16 → Before w true 15 17 → False :=
  fun z0 z1 z2 => cycle w true 16 15 17 z0 z2 z1

theorem c5193 (w : Witness) : Before w false 16 15 → Before w false 20 16 → Before w false 15 20 → False :=
  fun z0 z1 z2 => cycle w false 16 15 20 z0 z2 z1

theorem c5219 (w : Witness) : Before w true 18 15 → Before w true 19 18 → Before w true 15 19 → False :=
  fun z0 z1 z2 => cycle w true 18 15 19 z0 z2 z1

theorem c5223 (w : Witness) : Before w true 18 15 → Before w true 20 18 → Before w true 15 20 → False :=
  fun z0 z1 z2 => cycle w true 18 15 20 z0 z2 z1

theorem c5227 (w : Witness) : Before w true 18 15 → Before w true 21 18 → Before w true 15 21 → False :=
  fun z0 z1 z2 => cycle w true 18 15 21 z0 z2 z1

theorem c5231 (w : Witness) : Before w true 19 15 → Before w true 20 19 → Before w true 15 20 → False :=
  fun z0 z1 z2 => cycle w true 19 15 20 z0 z2 z1

theorem c5233 (w : Witness) : Before w false 19 15 → Before w false 21 19 → Before w false 15 21 → False :=
  fun z0 z1 z2 => cycle w false 19 15 21 z0 z2 z1

theorem c5239 (w : Witness) : Before w true 20 15 → Before w true 21 20 → Before w true 15 21 → False :=
  fun z0 z1 z2 => cycle w true 20 15 21 z0 z2 z1

theorem c5243 (w : Witness) : Before w true 17 16 → Before w true 18 17 → Before w true 16 18 → False :=
  fun z0 z1 z2 => cycle w true 17 16 18 z0 z2 z1

theorem c5251 (w : Witness) : Before w true 17 16 → Before w true 20 17 → Before w true 16 20 → False :=
  fun z0 z1 z2 => cycle w true 17 16 20 z0 z2 z1

theorem c5258 (w : Witness) : Before w false 16 18 → Before w false 18 19 → Before w false 19 16 → False :=
  fun z0 z1 z2 => cycle w false 16 18 19 z0 z1 z2

theorem c5259 (w : Witness) : Before w true 18 16 → Before w true 19 18 → Before w true 16 19 → False :=
  fun z0 z1 z2 => cycle w true 18 16 19 z0 z2 z1

theorem c5263 (w : Witness) : Before w true 18 16 → Before w true 20 18 → Before w true 16 20 → False :=
  fun z0 z1 z2 => cycle w true 18 16 20 z0 z2 z1

theorem c5271 (w : Witness) : Before w true 19 16 → Before w true 20 19 → Before w true 16 20 → False :=
  fun z0 z1 z2 => cycle w true 19 16 20 z0 z2 z1

theorem c5275 (w : Witness) : Before w true 19 16 → Before w true 21 19 → Before w true 16 21 → False :=
  fun z0 z1 z2 => cycle w true 19 16 21 z0 z2 z1

theorem c5277 (w : Witness) : Before w false 20 16 → Before w false 21 20 → Before w false 16 21 → False :=
  fun z0 z1 z2 => cycle w false 20 16 21 z0 z2 z1

theorem c5279 (w : Witness) : Before w true 20 16 → Before w true 21 20 → Before w true 16 21 → False :=
  fun z0 z1 z2 => cycle w true 20 16 21 z0 z2 z1

theorem c5282 (w : Witness) : Before w false 17 18 → Before w false 18 19 → Before w false 19 17 → False :=
  fun z0 z1 z2 => cycle w false 17 18 19 z0 z1 z2


end ThreeStacks.OrderProof
