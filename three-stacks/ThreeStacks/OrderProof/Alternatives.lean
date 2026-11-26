import ThreeStacks.CertificateBase

/- Generated natural-deduction proof. See verify/generate_order_proof.py. -/
set_option maxRecDepth 15000
set_option maxHeartbeats 8000000

namespace ThreeStacks.OrderProof

private theorem mem1 : 1 ∈ target 21 := .head _

private theorem mem2 : 2 ∈ target 21 := .tail _ (.head _)

private theorem mem3 : 3 ∈ target 21 := .tail _ (.tail _ (.head _))

private theorem mem4 : 4 ∈ target 21 := .tail _ (.tail _ (.tail _ (.head _)))

private theorem mem5 : 5 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

private theorem mem6 : 6 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

private theorem mem7 : 7 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))

private theorem mem8 : 8 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))

private theorem mem9 : 9 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))

private theorem mem10 : 10 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))

private theorem mem11 : 11 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))

private theorem mem12 : 12 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))

private theorem mem13 : 13 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))

private theorem mem14 : 14 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))

private theorem mem15 : 15 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))

private theorem mem16 : 16 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))

private theorem mem17 : 17 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))

private theorem mem18 : 18 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))

private theorem mem19 : 19 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))

private theorem mem20 : 20 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))

private theorem mem21 : 21 ∈ target 21 := .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))

theorem t1 (w : Witness) : Before w false 1 2 ∨ Before w false 2 1 :=
  alternatives w false 1 2 mem1 mem2 (by decide)

theorem t2 (w : Witness) : Before w false 1 3 ∨ Before w false 3 1 :=
  alternatives w false 1 3 mem1 mem3 (by decide)

theorem t3 (w : Witness) : Before w false 1 4 ∨ Before w false 4 1 :=
  alternatives w false 1 4 mem1 mem4 (by decide)

theorem t4 (w : Witness) : Before w false 1 5 ∨ Before w false 5 1 :=
  alternatives w false 1 5 mem1 mem5 (by decide)

theorem t5 (w : Witness) : Before w false 1 6 ∨ Before w false 6 1 :=
  alternatives w false 1 6 mem1 mem6 (by decide)

theorem t6 (w : Witness) : Before w false 1 7 ∨ Before w false 7 1 :=
  alternatives w false 1 7 mem1 mem7 (by decide)

theorem t7 (w : Witness) : Before w false 1 8 ∨ Before w false 8 1 :=
  alternatives w false 1 8 mem1 mem8 (by decide)

theorem t8 (w : Witness) : Before w false 1 9 ∨ Before w false 9 1 :=
  alternatives w false 1 9 mem1 mem9 (by decide)

theorem t9 (w : Witness) : Before w false 1 10 ∨ Before w false 10 1 :=
  alternatives w false 1 10 mem1 mem10 (by decide)

theorem t10 (w : Witness) : Before w false 1 11 ∨ Before w false 11 1 :=
  alternatives w false 1 11 mem1 mem11 (by decide)

theorem t11 (w : Witness) : Before w false 1 12 ∨ Before w false 12 1 :=
  alternatives w false 1 12 mem1 mem12 (by decide)

theorem t12 (w : Witness) : Before w false 1 13 ∨ Before w false 13 1 :=
  alternatives w false 1 13 mem1 mem13 (by decide)

theorem t13 (w : Witness) : Before w false 1 14 ∨ Before w false 14 1 :=
  alternatives w false 1 14 mem1 mem14 (by decide)

theorem t14 (w : Witness) : Before w false 1 15 ∨ Before w false 15 1 :=
  alternatives w false 1 15 mem1 mem15 (by decide)

theorem t15 (w : Witness) : Before w false 1 16 ∨ Before w false 16 1 :=
  alternatives w false 1 16 mem1 mem16 (by decide)

theorem t16 (w : Witness) : Before w false 1 17 ∨ Before w false 17 1 :=
  alternatives w false 1 17 mem1 mem17 (by decide)

theorem t17 (w : Witness) : Before w false 1 18 ∨ Before w false 18 1 :=
  alternatives w false 1 18 mem1 mem18 (by decide)

theorem t18 (w : Witness) : Before w false 1 19 ∨ Before w false 19 1 :=
  alternatives w false 1 19 mem1 mem19 (by decide)

theorem t19 (w : Witness) : Before w false 1 20 ∨ Before w false 20 1 :=
  alternatives w false 1 20 mem1 mem20 (by decide)

theorem t20 (w : Witness) : Before w false 1 21 ∨ Before w false 21 1 :=
  alternatives w false 1 21 mem1 mem21 (by decide)

theorem t21 (w : Witness) : Before w false 2 3 ∨ Before w false 3 2 :=
  alternatives w false 2 3 mem2 mem3 (by decide)

theorem t22 (w : Witness) : Before w false 2 4 ∨ Before w false 4 2 :=
  alternatives w false 2 4 mem2 mem4 (by decide)

theorem t23 (w : Witness) : Before w false 2 5 ∨ Before w false 5 2 :=
  alternatives w false 2 5 mem2 mem5 (by decide)

theorem t24 (w : Witness) : Before w false 2 6 ∨ Before w false 6 2 :=
  alternatives w false 2 6 mem2 mem6 (by decide)

theorem t25 (w : Witness) : Before w false 2 7 ∨ Before w false 7 2 :=
  alternatives w false 2 7 mem2 mem7 (by decide)

theorem t26 (w : Witness) : Before w false 2 8 ∨ Before w false 8 2 :=
  alternatives w false 2 8 mem2 mem8 (by decide)

theorem t27 (w : Witness) : Before w false 2 9 ∨ Before w false 9 2 :=
  alternatives w false 2 9 mem2 mem9 (by decide)

theorem t28 (w : Witness) : Before w false 2 10 ∨ Before w false 10 2 :=
  alternatives w false 2 10 mem2 mem10 (by decide)

theorem t29 (w : Witness) : Before w false 2 11 ∨ Before w false 11 2 :=
  alternatives w false 2 11 mem2 mem11 (by decide)

theorem t30 (w : Witness) : Before w false 2 12 ∨ Before w false 12 2 :=
  alternatives w false 2 12 mem2 mem12 (by decide)

theorem t31 (w : Witness) : Before w false 2 13 ∨ Before w false 13 2 :=
  alternatives w false 2 13 mem2 mem13 (by decide)

theorem t32 (w : Witness) : Before w false 2 14 ∨ Before w false 14 2 :=
  alternatives w false 2 14 mem2 mem14 (by decide)

theorem t33 (w : Witness) : Before w false 2 15 ∨ Before w false 15 2 :=
  alternatives w false 2 15 mem2 mem15 (by decide)

theorem t34 (w : Witness) : Before w false 2 16 ∨ Before w false 16 2 :=
  alternatives w false 2 16 mem2 mem16 (by decide)

theorem t35 (w : Witness) : Before w false 2 17 ∨ Before w false 17 2 :=
  alternatives w false 2 17 mem2 mem17 (by decide)

theorem t36 (w : Witness) : Before w false 2 18 ∨ Before w false 18 2 :=
  alternatives w false 2 18 mem2 mem18 (by decide)

theorem t37 (w : Witness) : Before w false 2 19 ∨ Before w false 19 2 :=
  alternatives w false 2 19 mem2 mem19 (by decide)

theorem t38 (w : Witness) : Before w false 2 20 ∨ Before w false 20 2 :=
  alternatives w false 2 20 mem2 mem20 (by decide)

theorem t39 (w : Witness) : Before w false 2 21 ∨ Before w false 21 2 :=
  alternatives w false 2 21 mem2 mem21 (by decide)

theorem t40 (w : Witness) : Before w false 3 4 ∨ Before w false 4 3 :=
  alternatives w false 3 4 mem3 mem4 (by decide)

theorem t41 (w : Witness) : Before w false 3 5 ∨ Before w false 5 3 :=
  alternatives w false 3 5 mem3 mem5 (by decide)

theorem t42 (w : Witness) : Before w false 3 6 ∨ Before w false 6 3 :=
  alternatives w false 3 6 mem3 mem6 (by decide)

theorem t43 (w : Witness) : Before w false 3 7 ∨ Before w false 7 3 :=
  alternatives w false 3 7 mem3 mem7 (by decide)

theorem t44 (w : Witness) : Before w false 3 8 ∨ Before w false 8 3 :=
  alternatives w false 3 8 mem3 mem8 (by decide)

theorem t45 (w : Witness) : Before w false 3 9 ∨ Before w false 9 3 :=
  alternatives w false 3 9 mem3 mem9 (by decide)

theorem t46 (w : Witness) : Before w false 3 10 ∨ Before w false 10 3 :=
  alternatives w false 3 10 mem3 mem10 (by decide)

theorem t47 (w : Witness) : Before w false 3 11 ∨ Before w false 11 3 :=
  alternatives w false 3 11 mem3 mem11 (by decide)

theorem t48 (w : Witness) : Before w false 3 12 ∨ Before w false 12 3 :=
  alternatives w false 3 12 mem3 mem12 (by decide)

theorem t49 (w : Witness) : Before w false 3 13 ∨ Before w false 13 3 :=
  alternatives w false 3 13 mem3 mem13 (by decide)

theorem t50 (w : Witness) : Before w false 3 14 ∨ Before w false 14 3 :=
  alternatives w false 3 14 mem3 mem14 (by decide)

theorem t51 (w : Witness) : Before w false 3 15 ∨ Before w false 15 3 :=
  alternatives w false 3 15 mem3 mem15 (by decide)

theorem t52 (w : Witness) : Before w false 3 16 ∨ Before w false 16 3 :=
  alternatives w false 3 16 mem3 mem16 (by decide)

theorem t53 (w : Witness) : Before w false 3 17 ∨ Before w false 17 3 :=
  alternatives w false 3 17 mem3 mem17 (by decide)

theorem t54 (w : Witness) : Before w false 3 18 ∨ Before w false 18 3 :=
  alternatives w false 3 18 mem3 mem18 (by decide)

theorem t55 (w : Witness) : Before w false 3 19 ∨ Before w false 19 3 :=
  alternatives w false 3 19 mem3 mem19 (by decide)

theorem t56 (w : Witness) : Before w false 3 20 ∨ Before w false 20 3 :=
  alternatives w false 3 20 mem3 mem20 (by decide)

theorem t57 (w : Witness) : Before w false 3 21 ∨ Before w false 21 3 :=
  alternatives w false 3 21 mem3 mem21 (by decide)

theorem t58 (w : Witness) : Before w false 4 5 ∨ Before w false 5 4 :=
  alternatives w false 4 5 mem4 mem5 (by decide)

theorem t59 (w : Witness) : Before w false 4 6 ∨ Before w false 6 4 :=
  alternatives w false 4 6 mem4 mem6 (by decide)

theorem t60 (w : Witness) : Before w false 4 7 ∨ Before w false 7 4 :=
  alternatives w false 4 7 mem4 mem7 (by decide)

theorem t61 (w : Witness) : Before w false 4 8 ∨ Before w false 8 4 :=
  alternatives w false 4 8 mem4 mem8 (by decide)

theorem t62 (w : Witness) : Before w false 4 9 ∨ Before w false 9 4 :=
  alternatives w false 4 9 mem4 mem9 (by decide)

theorem t63 (w : Witness) : Before w false 4 10 ∨ Before w false 10 4 :=
  alternatives w false 4 10 mem4 mem10 (by decide)

theorem t64 (w : Witness) : Before w false 4 11 ∨ Before w false 11 4 :=
  alternatives w false 4 11 mem4 mem11 (by decide)

theorem t65 (w : Witness) : Before w false 4 12 ∨ Before w false 12 4 :=
  alternatives w false 4 12 mem4 mem12 (by decide)

theorem t66 (w : Witness) : Before w false 4 13 ∨ Before w false 13 4 :=
  alternatives w false 4 13 mem4 mem13 (by decide)

theorem t67 (w : Witness) : Before w false 4 14 ∨ Before w false 14 4 :=
  alternatives w false 4 14 mem4 mem14 (by decide)

theorem t68 (w : Witness) : Before w false 4 15 ∨ Before w false 15 4 :=
  alternatives w false 4 15 mem4 mem15 (by decide)

theorem t69 (w : Witness) : Before w false 4 16 ∨ Before w false 16 4 :=
  alternatives w false 4 16 mem4 mem16 (by decide)

theorem t70 (w : Witness) : Before w false 4 17 ∨ Before w false 17 4 :=
  alternatives w false 4 17 mem4 mem17 (by decide)

theorem t71 (w : Witness) : Before w false 4 18 ∨ Before w false 18 4 :=
  alternatives w false 4 18 mem4 mem18 (by decide)

theorem t72 (w : Witness) : Before w false 4 19 ∨ Before w false 19 4 :=
  alternatives w false 4 19 mem4 mem19 (by decide)

theorem t73 (w : Witness) : Before w false 4 20 ∨ Before w false 20 4 :=
  alternatives w false 4 20 mem4 mem20 (by decide)

theorem t74 (w : Witness) : Before w false 4 21 ∨ Before w false 21 4 :=
  alternatives w false 4 21 mem4 mem21 (by decide)

theorem t75 (w : Witness) : Before w false 5 6 ∨ Before w false 6 5 :=
  alternatives w false 5 6 mem5 mem6 (by decide)

theorem t76 (w : Witness) : Before w false 5 7 ∨ Before w false 7 5 :=
  alternatives w false 5 7 mem5 mem7 (by decide)

theorem t77 (w : Witness) : Before w false 5 8 ∨ Before w false 8 5 :=
  alternatives w false 5 8 mem5 mem8 (by decide)

theorem t78 (w : Witness) : Before w false 5 9 ∨ Before w false 9 5 :=
  alternatives w false 5 9 mem5 mem9 (by decide)

theorem t79 (w : Witness) : Before w false 5 10 ∨ Before w false 10 5 :=
  alternatives w false 5 10 mem5 mem10 (by decide)

theorem t80 (w : Witness) : Before w false 5 11 ∨ Before w false 11 5 :=
  alternatives w false 5 11 mem5 mem11 (by decide)

theorem t81 (w : Witness) : Before w false 5 12 ∨ Before w false 12 5 :=
  alternatives w false 5 12 mem5 mem12 (by decide)

theorem t82 (w : Witness) : Before w false 5 13 ∨ Before w false 13 5 :=
  alternatives w false 5 13 mem5 mem13 (by decide)

theorem t83 (w : Witness) : Before w false 5 14 ∨ Before w false 14 5 :=
  alternatives w false 5 14 mem5 mem14 (by decide)

theorem t84 (w : Witness) : Before w false 5 15 ∨ Before w false 15 5 :=
  alternatives w false 5 15 mem5 mem15 (by decide)

theorem t85 (w : Witness) : Before w false 5 16 ∨ Before w false 16 5 :=
  alternatives w false 5 16 mem5 mem16 (by decide)

theorem t86 (w : Witness) : Before w false 5 17 ∨ Before w false 17 5 :=
  alternatives w false 5 17 mem5 mem17 (by decide)

theorem t87 (w : Witness) : Before w false 5 18 ∨ Before w false 18 5 :=
  alternatives w false 5 18 mem5 mem18 (by decide)

theorem t88 (w : Witness) : Before w false 5 19 ∨ Before w false 19 5 :=
  alternatives w false 5 19 mem5 mem19 (by decide)

theorem t89 (w : Witness) : Before w false 5 20 ∨ Before w false 20 5 :=
  alternatives w false 5 20 mem5 mem20 (by decide)

theorem t90 (w : Witness) : Before w false 5 21 ∨ Before w false 21 5 :=
  alternatives w false 5 21 mem5 mem21 (by decide)

theorem t91 (w : Witness) : Before w false 6 7 ∨ Before w false 7 6 :=
  alternatives w false 6 7 mem6 mem7 (by decide)

theorem t92 (w : Witness) : Before w false 6 8 ∨ Before w false 8 6 :=
  alternatives w false 6 8 mem6 mem8 (by decide)

theorem t93 (w : Witness) : Before w false 6 9 ∨ Before w false 9 6 :=
  alternatives w false 6 9 mem6 mem9 (by decide)

theorem t94 (w : Witness) : Before w false 6 10 ∨ Before w false 10 6 :=
  alternatives w false 6 10 mem6 mem10 (by decide)

theorem t95 (w : Witness) : Before w false 6 11 ∨ Before w false 11 6 :=
  alternatives w false 6 11 mem6 mem11 (by decide)

theorem t96 (w : Witness) : Before w false 6 12 ∨ Before w false 12 6 :=
  alternatives w false 6 12 mem6 mem12 (by decide)

theorem t97 (w : Witness) : Before w false 6 13 ∨ Before w false 13 6 :=
  alternatives w false 6 13 mem6 mem13 (by decide)

theorem t98 (w : Witness) : Before w false 6 14 ∨ Before w false 14 6 :=
  alternatives w false 6 14 mem6 mem14 (by decide)

theorem t99 (w : Witness) : Before w false 6 15 ∨ Before w false 15 6 :=
  alternatives w false 6 15 mem6 mem15 (by decide)

theorem t100 (w : Witness) : Before w false 6 16 ∨ Before w false 16 6 :=
  alternatives w false 6 16 mem6 mem16 (by decide)

theorem t101 (w : Witness) : Before w false 6 17 ∨ Before w false 17 6 :=
  alternatives w false 6 17 mem6 mem17 (by decide)

theorem t102 (w : Witness) : Before w false 6 18 ∨ Before w false 18 6 :=
  alternatives w false 6 18 mem6 mem18 (by decide)

theorem t103 (w : Witness) : Before w false 6 19 ∨ Before w false 19 6 :=
  alternatives w false 6 19 mem6 mem19 (by decide)

theorem t104 (w : Witness) : Before w false 6 20 ∨ Before w false 20 6 :=
  alternatives w false 6 20 mem6 mem20 (by decide)

theorem t105 (w : Witness) : Before w false 6 21 ∨ Before w false 21 6 :=
  alternatives w false 6 21 mem6 mem21 (by decide)

theorem t106 (w : Witness) : Before w false 7 8 ∨ Before w false 8 7 :=
  alternatives w false 7 8 mem7 mem8 (by decide)

theorem t107 (w : Witness) : Before w false 7 9 ∨ Before w false 9 7 :=
  alternatives w false 7 9 mem7 mem9 (by decide)

theorem t108 (w : Witness) : Before w false 7 10 ∨ Before w false 10 7 :=
  alternatives w false 7 10 mem7 mem10 (by decide)

theorem t109 (w : Witness) : Before w false 7 11 ∨ Before w false 11 7 :=
  alternatives w false 7 11 mem7 mem11 (by decide)

theorem t110 (w : Witness) : Before w false 7 12 ∨ Before w false 12 7 :=
  alternatives w false 7 12 mem7 mem12 (by decide)

theorem t111 (w : Witness) : Before w false 7 13 ∨ Before w false 13 7 :=
  alternatives w false 7 13 mem7 mem13 (by decide)

theorem t112 (w : Witness) : Before w false 7 14 ∨ Before w false 14 7 :=
  alternatives w false 7 14 mem7 mem14 (by decide)

theorem t113 (w : Witness) : Before w false 7 15 ∨ Before w false 15 7 :=
  alternatives w false 7 15 mem7 mem15 (by decide)

theorem t114 (w : Witness) : Before w false 7 16 ∨ Before w false 16 7 :=
  alternatives w false 7 16 mem7 mem16 (by decide)

theorem t115 (w : Witness) : Before w false 7 17 ∨ Before w false 17 7 :=
  alternatives w false 7 17 mem7 mem17 (by decide)

theorem t116 (w : Witness) : Before w false 7 18 ∨ Before w false 18 7 :=
  alternatives w false 7 18 mem7 mem18 (by decide)

theorem t117 (w : Witness) : Before w false 7 19 ∨ Before w false 19 7 :=
  alternatives w false 7 19 mem7 mem19 (by decide)

theorem t118 (w : Witness) : Before w false 7 20 ∨ Before w false 20 7 :=
  alternatives w false 7 20 mem7 mem20 (by decide)

theorem t119 (w : Witness) : Before w false 7 21 ∨ Before w false 21 7 :=
  alternatives w false 7 21 mem7 mem21 (by decide)

theorem t120 (w : Witness) : Before w false 8 9 ∨ Before w false 9 8 :=
  alternatives w false 8 9 mem8 mem9 (by decide)

theorem t121 (w : Witness) : Before w false 8 10 ∨ Before w false 10 8 :=
  alternatives w false 8 10 mem8 mem10 (by decide)

theorem t122 (w : Witness) : Before w false 8 11 ∨ Before w false 11 8 :=
  alternatives w false 8 11 mem8 mem11 (by decide)

theorem t123 (w : Witness) : Before w false 8 12 ∨ Before w false 12 8 :=
  alternatives w false 8 12 mem8 mem12 (by decide)

theorem t124 (w : Witness) : Before w false 8 13 ∨ Before w false 13 8 :=
  alternatives w false 8 13 mem8 mem13 (by decide)

theorem t125 (w : Witness) : Before w false 8 14 ∨ Before w false 14 8 :=
  alternatives w false 8 14 mem8 mem14 (by decide)

theorem t126 (w : Witness) : Before w false 8 15 ∨ Before w false 15 8 :=
  alternatives w false 8 15 mem8 mem15 (by decide)

theorem t127 (w : Witness) : Before w false 8 16 ∨ Before w false 16 8 :=
  alternatives w false 8 16 mem8 mem16 (by decide)

theorem t128 (w : Witness) : Before w false 8 17 ∨ Before w false 17 8 :=
  alternatives w false 8 17 mem8 mem17 (by decide)

theorem t129 (w : Witness) : Before w false 8 18 ∨ Before w false 18 8 :=
  alternatives w false 8 18 mem8 mem18 (by decide)

theorem t130 (w : Witness) : Before w false 8 19 ∨ Before w false 19 8 :=
  alternatives w false 8 19 mem8 mem19 (by decide)

theorem t131 (w : Witness) : Before w false 8 20 ∨ Before w false 20 8 :=
  alternatives w false 8 20 mem8 mem20 (by decide)

theorem t132 (w : Witness) : Before w false 8 21 ∨ Before w false 21 8 :=
  alternatives w false 8 21 mem8 mem21 (by decide)

theorem t133 (w : Witness) : Before w false 9 10 ∨ Before w false 10 9 :=
  alternatives w false 9 10 mem9 mem10 (by decide)

theorem t134 (w : Witness) : Before w false 9 11 ∨ Before w false 11 9 :=
  alternatives w false 9 11 mem9 mem11 (by decide)

theorem t135 (w : Witness) : Before w false 9 12 ∨ Before w false 12 9 :=
  alternatives w false 9 12 mem9 mem12 (by decide)

theorem t136 (w : Witness) : Before w false 9 13 ∨ Before w false 13 9 :=
  alternatives w false 9 13 mem9 mem13 (by decide)

theorem t137 (w : Witness) : Before w false 9 14 ∨ Before w false 14 9 :=
  alternatives w false 9 14 mem9 mem14 (by decide)

theorem t138 (w : Witness) : Before w false 9 15 ∨ Before w false 15 9 :=
  alternatives w false 9 15 mem9 mem15 (by decide)

theorem t139 (w : Witness) : Before w false 9 16 ∨ Before w false 16 9 :=
  alternatives w false 9 16 mem9 mem16 (by decide)

theorem t140 (w : Witness) : Before w false 9 17 ∨ Before w false 17 9 :=
  alternatives w false 9 17 mem9 mem17 (by decide)

theorem t141 (w : Witness) : Before w false 9 18 ∨ Before w false 18 9 :=
  alternatives w false 9 18 mem9 mem18 (by decide)

theorem t142 (w : Witness) : Before w false 9 19 ∨ Before w false 19 9 :=
  alternatives w false 9 19 mem9 mem19 (by decide)

theorem t143 (w : Witness) : Before w false 9 20 ∨ Before w false 20 9 :=
  alternatives w false 9 20 mem9 mem20 (by decide)

theorem t144 (w : Witness) : Before w false 9 21 ∨ Before w false 21 9 :=
  alternatives w false 9 21 mem9 mem21 (by decide)

theorem t145 (w : Witness) : Before w false 10 11 ∨ Before w false 11 10 :=
  alternatives w false 10 11 mem10 mem11 (by decide)

theorem t146 (w : Witness) : Before w false 10 12 ∨ Before w false 12 10 :=
  alternatives w false 10 12 mem10 mem12 (by decide)

theorem t147 (w : Witness) : Before w false 10 13 ∨ Before w false 13 10 :=
  alternatives w false 10 13 mem10 mem13 (by decide)

theorem t148 (w : Witness) : Before w false 10 14 ∨ Before w false 14 10 :=
  alternatives w false 10 14 mem10 mem14 (by decide)

theorem t149 (w : Witness) : Before w false 10 15 ∨ Before w false 15 10 :=
  alternatives w false 10 15 mem10 mem15 (by decide)

theorem t150 (w : Witness) : Before w false 10 16 ∨ Before w false 16 10 :=
  alternatives w false 10 16 mem10 mem16 (by decide)

theorem t151 (w : Witness) : Before w false 10 17 ∨ Before w false 17 10 :=
  alternatives w false 10 17 mem10 mem17 (by decide)

theorem t152 (w : Witness) : Before w false 10 18 ∨ Before w false 18 10 :=
  alternatives w false 10 18 mem10 mem18 (by decide)

theorem t153 (w : Witness) : Before w false 10 19 ∨ Before w false 19 10 :=
  alternatives w false 10 19 mem10 mem19 (by decide)

theorem t154 (w : Witness) : Before w false 10 20 ∨ Before w false 20 10 :=
  alternatives w false 10 20 mem10 mem20 (by decide)

theorem t155 (w : Witness) : Before w false 10 21 ∨ Before w false 21 10 :=
  alternatives w false 10 21 mem10 mem21 (by decide)

theorem t156 (w : Witness) : Before w false 11 12 ∨ Before w false 12 11 :=
  alternatives w false 11 12 mem11 mem12 (by decide)

theorem t157 (w : Witness) : Before w false 11 13 ∨ Before w false 13 11 :=
  alternatives w false 11 13 mem11 mem13 (by decide)

theorem t158 (w : Witness) : Before w false 11 14 ∨ Before w false 14 11 :=
  alternatives w false 11 14 mem11 mem14 (by decide)

theorem t159 (w : Witness) : Before w false 11 15 ∨ Before w false 15 11 :=
  alternatives w false 11 15 mem11 mem15 (by decide)

theorem t160 (w : Witness) : Before w false 11 16 ∨ Before w false 16 11 :=
  alternatives w false 11 16 mem11 mem16 (by decide)

theorem t161 (w : Witness) : Before w false 11 17 ∨ Before w false 17 11 :=
  alternatives w false 11 17 mem11 mem17 (by decide)

theorem t162 (w : Witness) : Before w false 11 18 ∨ Before w false 18 11 :=
  alternatives w false 11 18 mem11 mem18 (by decide)

theorem t163 (w : Witness) : Before w false 11 19 ∨ Before w false 19 11 :=
  alternatives w false 11 19 mem11 mem19 (by decide)

theorem t164 (w : Witness) : Before w false 11 20 ∨ Before w false 20 11 :=
  alternatives w false 11 20 mem11 mem20 (by decide)

theorem t165 (w : Witness) : Before w false 11 21 ∨ Before w false 21 11 :=
  alternatives w false 11 21 mem11 mem21 (by decide)

theorem t166 (w : Witness) : Before w false 12 13 ∨ Before w false 13 12 :=
  alternatives w false 12 13 mem12 mem13 (by decide)

theorem t167 (w : Witness) : Before w false 12 14 ∨ Before w false 14 12 :=
  alternatives w false 12 14 mem12 mem14 (by decide)

theorem t168 (w : Witness) : Before w false 12 15 ∨ Before w false 15 12 :=
  alternatives w false 12 15 mem12 mem15 (by decide)

theorem t169 (w : Witness) : Before w false 12 16 ∨ Before w false 16 12 :=
  alternatives w false 12 16 mem12 mem16 (by decide)

theorem t170 (w : Witness) : Before w false 12 17 ∨ Before w false 17 12 :=
  alternatives w false 12 17 mem12 mem17 (by decide)

theorem t171 (w : Witness) : Before w false 12 18 ∨ Before w false 18 12 :=
  alternatives w false 12 18 mem12 mem18 (by decide)

theorem t172 (w : Witness) : Before w false 12 19 ∨ Before w false 19 12 :=
  alternatives w false 12 19 mem12 mem19 (by decide)

theorem t173 (w : Witness) : Before w false 12 20 ∨ Before w false 20 12 :=
  alternatives w false 12 20 mem12 mem20 (by decide)

theorem t174 (w : Witness) : Before w false 12 21 ∨ Before w false 21 12 :=
  alternatives w false 12 21 mem12 mem21 (by decide)

theorem t175 (w : Witness) : Before w false 13 14 ∨ Before w false 14 13 :=
  alternatives w false 13 14 mem13 mem14 (by decide)

theorem t176 (w : Witness) : Before w false 13 15 ∨ Before w false 15 13 :=
  alternatives w false 13 15 mem13 mem15 (by decide)

theorem t177 (w : Witness) : Before w false 13 16 ∨ Before w false 16 13 :=
  alternatives w false 13 16 mem13 mem16 (by decide)

theorem t178 (w : Witness) : Before w false 13 17 ∨ Before w false 17 13 :=
  alternatives w false 13 17 mem13 mem17 (by decide)

theorem t179 (w : Witness) : Before w false 13 18 ∨ Before w false 18 13 :=
  alternatives w false 13 18 mem13 mem18 (by decide)

theorem t180 (w : Witness) : Before w false 13 19 ∨ Before w false 19 13 :=
  alternatives w false 13 19 mem13 mem19 (by decide)

theorem t181 (w : Witness) : Before w false 13 20 ∨ Before w false 20 13 :=
  alternatives w false 13 20 mem13 mem20 (by decide)

theorem t182 (w : Witness) : Before w false 13 21 ∨ Before w false 21 13 :=
  alternatives w false 13 21 mem13 mem21 (by decide)

theorem t183 (w : Witness) : Before w false 14 15 ∨ Before w false 15 14 :=
  alternatives w false 14 15 mem14 mem15 (by decide)

theorem t184 (w : Witness) : Before w false 14 16 ∨ Before w false 16 14 :=
  alternatives w false 14 16 mem14 mem16 (by decide)

theorem t185 (w : Witness) : Before w false 14 17 ∨ Before w false 17 14 :=
  alternatives w false 14 17 mem14 mem17 (by decide)

theorem t186 (w : Witness) : Before w false 14 18 ∨ Before w false 18 14 :=
  alternatives w false 14 18 mem14 mem18 (by decide)

theorem t187 (w : Witness) : Before w false 14 19 ∨ Before w false 19 14 :=
  alternatives w false 14 19 mem14 mem19 (by decide)

theorem t188 (w : Witness) : Before w false 14 20 ∨ Before w false 20 14 :=
  alternatives w false 14 20 mem14 mem20 (by decide)

theorem t189 (w : Witness) : Before w false 14 21 ∨ Before w false 21 14 :=
  alternatives w false 14 21 mem14 mem21 (by decide)

theorem t190 (w : Witness) : Before w false 15 16 ∨ Before w false 16 15 :=
  alternatives w false 15 16 mem15 mem16 (by decide)

theorem t191 (w : Witness) : Before w false 15 17 ∨ Before w false 17 15 :=
  alternatives w false 15 17 mem15 mem17 (by decide)

theorem t192 (w : Witness) : Before w false 15 18 ∨ Before w false 18 15 :=
  alternatives w false 15 18 mem15 mem18 (by decide)

theorem t193 (w : Witness) : Before w false 15 19 ∨ Before w false 19 15 :=
  alternatives w false 15 19 mem15 mem19 (by decide)

theorem t194 (w : Witness) : Before w false 15 20 ∨ Before w false 20 15 :=
  alternatives w false 15 20 mem15 mem20 (by decide)

theorem t195 (w : Witness) : Before w false 15 21 ∨ Before w false 21 15 :=
  alternatives w false 15 21 mem15 mem21 (by decide)

theorem t196 (w : Witness) : Before w false 16 17 ∨ Before w false 17 16 :=
  alternatives w false 16 17 mem16 mem17 (by decide)

theorem t197 (w : Witness) : Before w false 16 18 ∨ Before w false 18 16 :=
  alternatives w false 16 18 mem16 mem18 (by decide)

theorem t198 (w : Witness) : Before w false 16 19 ∨ Before w false 19 16 :=
  alternatives w false 16 19 mem16 mem19 (by decide)

theorem t199 (w : Witness) : Before w false 16 20 ∨ Before w false 20 16 :=
  alternatives w false 16 20 mem16 mem20 (by decide)

theorem t200 (w : Witness) : Before w false 16 21 ∨ Before w false 21 16 :=
  alternatives w false 16 21 mem16 mem21 (by decide)

theorem t201 (w : Witness) : Before w false 17 18 ∨ Before w false 18 17 :=
  alternatives w false 17 18 mem17 mem18 (by decide)

theorem t202 (w : Witness) : Before w false 17 19 ∨ Before w false 19 17 :=
  alternatives w false 17 19 mem17 mem19 (by decide)

theorem t203 (w : Witness) : Before w false 17 20 ∨ Before w false 20 17 :=
  alternatives w false 17 20 mem17 mem20 (by decide)

theorem t204 (w : Witness) : Before w false 17 21 ∨ Before w false 21 17 :=
  alternatives w false 17 21 mem17 mem21 (by decide)

theorem t205 (w : Witness) : Before w false 18 19 ∨ Before w false 19 18 :=
  alternatives w false 18 19 mem18 mem19 (by decide)

theorem t206 (w : Witness) : Before w false 18 20 ∨ Before w false 20 18 :=
  alternatives w false 18 20 mem18 mem20 (by decide)

theorem t207 (w : Witness) : Before w false 18 21 ∨ Before w false 21 18 :=
  alternatives w false 18 21 mem18 mem21 (by decide)

theorem t208 (w : Witness) : Before w false 19 20 ∨ Before w false 20 19 :=
  alternatives w false 19 20 mem19 mem20 (by decide)

theorem t209 (w : Witness) : Before w false 19 21 ∨ Before w false 21 19 :=
  alternatives w false 19 21 mem19 mem21 (by decide)

theorem t210 (w : Witness) : Before w false 20 21 ∨ Before w false 21 20 :=
  alternatives w false 20 21 mem20 mem21 (by decide)

theorem t211 (w : Witness) : Before w true 1 2 ∨ Before w true 2 1 :=
  alternatives w true 1 2 mem1 mem2 (by decide)

theorem t212 (w : Witness) : Before w true 1 3 ∨ Before w true 3 1 :=
  alternatives w true 1 3 mem1 mem3 (by decide)

theorem t213 (w : Witness) : Before w true 1 4 ∨ Before w true 4 1 :=
  alternatives w true 1 4 mem1 mem4 (by decide)

theorem t214 (w : Witness) : Before w true 1 5 ∨ Before w true 5 1 :=
  alternatives w true 1 5 mem1 mem5 (by decide)

theorem t215 (w : Witness) : Before w true 1 6 ∨ Before w true 6 1 :=
  alternatives w true 1 6 mem1 mem6 (by decide)

theorem t216 (w : Witness) : Before w true 1 7 ∨ Before w true 7 1 :=
  alternatives w true 1 7 mem1 mem7 (by decide)

theorem t217 (w : Witness) : Before w true 1 8 ∨ Before w true 8 1 :=
  alternatives w true 1 8 mem1 mem8 (by decide)

theorem t218 (w : Witness) : Before w true 1 9 ∨ Before w true 9 1 :=
  alternatives w true 1 9 mem1 mem9 (by decide)

theorem t219 (w : Witness) : Before w true 1 10 ∨ Before w true 10 1 :=
  alternatives w true 1 10 mem1 mem10 (by decide)

theorem t220 (w : Witness) : Before w true 1 11 ∨ Before w true 11 1 :=
  alternatives w true 1 11 mem1 mem11 (by decide)

theorem t221 (w : Witness) : Before w true 1 12 ∨ Before w true 12 1 :=
  alternatives w true 1 12 mem1 mem12 (by decide)

theorem t222 (w : Witness) : Before w true 1 13 ∨ Before w true 13 1 :=
  alternatives w true 1 13 mem1 mem13 (by decide)

theorem t223 (w : Witness) : Before w true 1 14 ∨ Before w true 14 1 :=
  alternatives w true 1 14 mem1 mem14 (by decide)

theorem t224 (w : Witness) : Before w true 1 15 ∨ Before w true 15 1 :=
  alternatives w true 1 15 mem1 mem15 (by decide)

theorem t225 (w : Witness) : Before w true 1 16 ∨ Before w true 16 1 :=
  alternatives w true 1 16 mem1 mem16 (by decide)

theorem t226 (w : Witness) : Before w true 1 17 ∨ Before w true 17 1 :=
  alternatives w true 1 17 mem1 mem17 (by decide)

theorem t227 (w : Witness) : Before w true 1 18 ∨ Before w true 18 1 :=
  alternatives w true 1 18 mem1 mem18 (by decide)

theorem t228 (w : Witness) : Before w true 1 19 ∨ Before w true 19 1 :=
  alternatives w true 1 19 mem1 mem19 (by decide)

theorem t229 (w : Witness) : Before w true 1 20 ∨ Before w true 20 1 :=
  alternatives w true 1 20 mem1 mem20 (by decide)

theorem t230 (w : Witness) : Before w true 1 21 ∨ Before w true 21 1 :=
  alternatives w true 1 21 mem1 mem21 (by decide)

theorem t231 (w : Witness) : Before w true 2 3 ∨ Before w true 3 2 :=
  alternatives w true 2 3 mem2 mem3 (by decide)

theorem t232 (w : Witness) : Before w true 2 4 ∨ Before w true 4 2 :=
  alternatives w true 2 4 mem2 mem4 (by decide)

theorem t233 (w : Witness) : Before w true 2 5 ∨ Before w true 5 2 :=
  alternatives w true 2 5 mem2 mem5 (by decide)

theorem t234 (w : Witness) : Before w true 2 6 ∨ Before w true 6 2 :=
  alternatives w true 2 6 mem2 mem6 (by decide)

theorem t235 (w : Witness) : Before w true 2 7 ∨ Before w true 7 2 :=
  alternatives w true 2 7 mem2 mem7 (by decide)

theorem t236 (w : Witness) : Before w true 2 8 ∨ Before w true 8 2 :=
  alternatives w true 2 8 mem2 mem8 (by decide)

theorem t237 (w : Witness) : Before w true 2 9 ∨ Before w true 9 2 :=
  alternatives w true 2 9 mem2 mem9 (by decide)

theorem t238 (w : Witness) : Before w true 2 10 ∨ Before w true 10 2 :=
  alternatives w true 2 10 mem2 mem10 (by decide)

theorem t239 (w : Witness) : Before w true 2 11 ∨ Before w true 11 2 :=
  alternatives w true 2 11 mem2 mem11 (by decide)

theorem t240 (w : Witness) : Before w true 2 12 ∨ Before w true 12 2 :=
  alternatives w true 2 12 mem2 mem12 (by decide)

theorem t241 (w : Witness) : Before w true 2 13 ∨ Before w true 13 2 :=
  alternatives w true 2 13 mem2 mem13 (by decide)

theorem t242 (w : Witness) : Before w true 2 14 ∨ Before w true 14 2 :=
  alternatives w true 2 14 mem2 mem14 (by decide)

theorem t243 (w : Witness) : Before w true 2 15 ∨ Before w true 15 2 :=
  alternatives w true 2 15 mem2 mem15 (by decide)

theorem t244 (w : Witness) : Before w true 2 16 ∨ Before w true 16 2 :=
  alternatives w true 2 16 mem2 mem16 (by decide)

theorem t245 (w : Witness) : Before w true 2 17 ∨ Before w true 17 2 :=
  alternatives w true 2 17 mem2 mem17 (by decide)

theorem t246 (w : Witness) : Before w true 2 18 ∨ Before w true 18 2 :=
  alternatives w true 2 18 mem2 mem18 (by decide)

theorem t247 (w : Witness) : Before w true 2 19 ∨ Before w true 19 2 :=
  alternatives w true 2 19 mem2 mem19 (by decide)

theorem t248 (w : Witness) : Before w true 2 20 ∨ Before w true 20 2 :=
  alternatives w true 2 20 mem2 mem20 (by decide)

theorem t249 (w : Witness) : Before w true 2 21 ∨ Before w true 21 2 :=
  alternatives w true 2 21 mem2 mem21 (by decide)

theorem t250 (w : Witness) : Before w true 3 4 ∨ Before w true 4 3 :=
  alternatives w true 3 4 mem3 mem4 (by decide)

theorem t251 (w : Witness) : Before w true 3 5 ∨ Before w true 5 3 :=
  alternatives w true 3 5 mem3 mem5 (by decide)

theorem t252 (w : Witness) : Before w true 3 6 ∨ Before w true 6 3 :=
  alternatives w true 3 6 mem3 mem6 (by decide)

theorem t253 (w : Witness) : Before w true 3 7 ∨ Before w true 7 3 :=
  alternatives w true 3 7 mem3 mem7 (by decide)

theorem t254 (w : Witness) : Before w true 3 8 ∨ Before w true 8 3 :=
  alternatives w true 3 8 mem3 mem8 (by decide)

theorem t255 (w : Witness) : Before w true 3 9 ∨ Before w true 9 3 :=
  alternatives w true 3 9 mem3 mem9 (by decide)

theorem t256 (w : Witness) : Before w true 3 10 ∨ Before w true 10 3 :=
  alternatives w true 3 10 mem3 mem10 (by decide)

theorem t257 (w : Witness) : Before w true 3 11 ∨ Before w true 11 3 :=
  alternatives w true 3 11 mem3 mem11 (by decide)

theorem t258 (w : Witness) : Before w true 3 12 ∨ Before w true 12 3 :=
  alternatives w true 3 12 mem3 mem12 (by decide)

theorem t259 (w : Witness) : Before w true 3 13 ∨ Before w true 13 3 :=
  alternatives w true 3 13 mem3 mem13 (by decide)

theorem t260 (w : Witness) : Before w true 3 14 ∨ Before w true 14 3 :=
  alternatives w true 3 14 mem3 mem14 (by decide)

theorem t261 (w : Witness) : Before w true 3 15 ∨ Before w true 15 3 :=
  alternatives w true 3 15 mem3 mem15 (by decide)

theorem t262 (w : Witness) : Before w true 3 16 ∨ Before w true 16 3 :=
  alternatives w true 3 16 mem3 mem16 (by decide)

theorem t263 (w : Witness) : Before w true 3 17 ∨ Before w true 17 3 :=
  alternatives w true 3 17 mem3 mem17 (by decide)

theorem t264 (w : Witness) : Before w true 3 18 ∨ Before w true 18 3 :=
  alternatives w true 3 18 mem3 mem18 (by decide)

theorem t265 (w : Witness) : Before w true 3 19 ∨ Before w true 19 3 :=
  alternatives w true 3 19 mem3 mem19 (by decide)

theorem t266 (w : Witness) : Before w true 3 20 ∨ Before w true 20 3 :=
  alternatives w true 3 20 mem3 mem20 (by decide)

theorem t267 (w : Witness) : Before w true 3 21 ∨ Before w true 21 3 :=
  alternatives w true 3 21 mem3 mem21 (by decide)

theorem t268 (w : Witness) : Before w true 4 5 ∨ Before w true 5 4 :=
  alternatives w true 4 5 mem4 mem5 (by decide)

theorem t269 (w : Witness) : Before w true 4 6 ∨ Before w true 6 4 :=
  alternatives w true 4 6 mem4 mem6 (by decide)

theorem t270 (w : Witness) : Before w true 4 7 ∨ Before w true 7 4 :=
  alternatives w true 4 7 mem4 mem7 (by decide)

theorem t271 (w : Witness) : Before w true 4 8 ∨ Before w true 8 4 :=
  alternatives w true 4 8 mem4 mem8 (by decide)

theorem t272 (w : Witness) : Before w true 4 9 ∨ Before w true 9 4 :=
  alternatives w true 4 9 mem4 mem9 (by decide)

theorem t273 (w : Witness) : Before w true 4 10 ∨ Before w true 10 4 :=
  alternatives w true 4 10 mem4 mem10 (by decide)

theorem t274 (w : Witness) : Before w true 4 11 ∨ Before w true 11 4 :=
  alternatives w true 4 11 mem4 mem11 (by decide)

theorem t275 (w : Witness) : Before w true 4 12 ∨ Before w true 12 4 :=
  alternatives w true 4 12 mem4 mem12 (by decide)

theorem t276 (w : Witness) : Before w true 4 13 ∨ Before w true 13 4 :=
  alternatives w true 4 13 mem4 mem13 (by decide)

theorem t277 (w : Witness) : Before w true 4 14 ∨ Before w true 14 4 :=
  alternatives w true 4 14 mem4 mem14 (by decide)

theorem t278 (w : Witness) : Before w true 4 15 ∨ Before w true 15 4 :=
  alternatives w true 4 15 mem4 mem15 (by decide)

theorem t279 (w : Witness) : Before w true 4 16 ∨ Before w true 16 4 :=
  alternatives w true 4 16 mem4 mem16 (by decide)

theorem t280 (w : Witness) : Before w true 4 17 ∨ Before w true 17 4 :=
  alternatives w true 4 17 mem4 mem17 (by decide)

theorem t281 (w : Witness) : Before w true 4 18 ∨ Before w true 18 4 :=
  alternatives w true 4 18 mem4 mem18 (by decide)

theorem t282 (w : Witness) : Before w true 4 19 ∨ Before w true 19 4 :=
  alternatives w true 4 19 mem4 mem19 (by decide)

theorem t283 (w : Witness) : Before w true 4 20 ∨ Before w true 20 4 :=
  alternatives w true 4 20 mem4 mem20 (by decide)

theorem t284 (w : Witness) : Before w true 4 21 ∨ Before w true 21 4 :=
  alternatives w true 4 21 mem4 mem21 (by decide)

theorem t285 (w : Witness) : Before w true 5 6 ∨ Before w true 6 5 :=
  alternatives w true 5 6 mem5 mem6 (by decide)

theorem t286 (w : Witness) : Before w true 5 7 ∨ Before w true 7 5 :=
  alternatives w true 5 7 mem5 mem7 (by decide)

theorem t287 (w : Witness) : Before w true 5 8 ∨ Before w true 8 5 :=
  alternatives w true 5 8 mem5 mem8 (by decide)

theorem t288 (w : Witness) : Before w true 5 9 ∨ Before w true 9 5 :=
  alternatives w true 5 9 mem5 mem9 (by decide)

theorem t289 (w : Witness) : Before w true 5 10 ∨ Before w true 10 5 :=
  alternatives w true 5 10 mem5 mem10 (by decide)

theorem t290 (w : Witness) : Before w true 5 11 ∨ Before w true 11 5 :=
  alternatives w true 5 11 mem5 mem11 (by decide)

theorem t291 (w : Witness) : Before w true 5 12 ∨ Before w true 12 5 :=
  alternatives w true 5 12 mem5 mem12 (by decide)

theorem t292 (w : Witness) : Before w true 5 13 ∨ Before w true 13 5 :=
  alternatives w true 5 13 mem5 mem13 (by decide)

theorem t293 (w : Witness) : Before w true 5 14 ∨ Before w true 14 5 :=
  alternatives w true 5 14 mem5 mem14 (by decide)

theorem t294 (w : Witness) : Before w true 5 15 ∨ Before w true 15 5 :=
  alternatives w true 5 15 mem5 mem15 (by decide)

theorem t295 (w : Witness) : Before w true 5 16 ∨ Before w true 16 5 :=
  alternatives w true 5 16 mem5 mem16 (by decide)

theorem t296 (w : Witness) : Before w true 5 17 ∨ Before w true 17 5 :=
  alternatives w true 5 17 mem5 mem17 (by decide)

theorem t297 (w : Witness) : Before w true 5 18 ∨ Before w true 18 5 :=
  alternatives w true 5 18 mem5 mem18 (by decide)

theorem t298 (w : Witness) : Before w true 5 19 ∨ Before w true 19 5 :=
  alternatives w true 5 19 mem5 mem19 (by decide)

theorem t299 (w : Witness) : Before w true 5 20 ∨ Before w true 20 5 :=
  alternatives w true 5 20 mem5 mem20 (by decide)

theorem t300 (w : Witness) : Before w true 5 21 ∨ Before w true 21 5 :=
  alternatives w true 5 21 mem5 mem21 (by decide)

theorem t301 (w : Witness) : Before w true 6 7 ∨ Before w true 7 6 :=
  alternatives w true 6 7 mem6 mem7 (by decide)

theorem t302 (w : Witness) : Before w true 6 8 ∨ Before w true 8 6 :=
  alternatives w true 6 8 mem6 mem8 (by decide)

theorem t303 (w : Witness) : Before w true 6 9 ∨ Before w true 9 6 :=
  alternatives w true 6 9 mem6 mem9 (by decide)

theorem t304 (w : Witness) : Before w true 6 10 ∨ Before w true 10 6 :=
  alternatives w true 6 10 mem6 mem10 (by decide)

theorem t305 (w : Witness) : Before w true 6 11 ∨ Before w true 11 6 :=
  alternatives w true 6 11 mem6 mem11 (by decide)

theorem t306 (w : Witness) : Before w true 6 12 ∨ Before w true 12 6 :=
  alternatives w true 6 12 mem6 mem12 (by decide)

theorem t307 (w : Witness) : Before w true 6 13 ∨ Before w true 13 6 :=
  alternatives w true 6 13 mem6 mem13 (by decide)

theorem t308 (w : Witness) : Before w true 6 14 ∨ Before w true 14 6 :=
  alternatives w true 6 14 mem6 mem14 (by decide)

theorem t309 (w : Witness) : Before w true 6 15 ∨ Before w true 15 6 :=
  alternatives w true 6 15 mem6 mem15 (by decide)

theorem t310 (w : Witness) : Before w true 6 16 ∨ Before w true 16 6 :=
  alternatives w true 6 16 mem6 mem16 (by decide)

theorem t311 (w : Witness) : Before w true 6 17 ∨ Before w true 17 6 :=
  alternatives w true 6 17 mem6 mem17 (by decide)

theorem t312 (w : Witness) : Before w true 6 18 ∨ Before w true 18 6 :=
  alternatives w true 6 18 mem6 mem18 (by decide)

theorem t313 (w : Witness) : Before w true 6 19 ∨ Before w true 19 6 :=
  alternatives w true 6 19 mem6 mem19 (by decide)

theorem t314 (w : Witness) : Before w true 6 20 ∨ Before w true 20 6 :=
  alternatives w true 6 20 mem6 mem20 (by decide)

theorem t315 (w : Witness) : Before w true 6 21 ∨ Before w true 21 6 :=
  alternatives w true 6 21 mem6 mem21 (by decide)

theorem t316 (w : Witness) : Before w true 7 8 ∨ Before w true 8 7 :=
  alternatives w true 7 8 mem7 mem8 (by decide)

theorem t317 (w : Witness) : Before w true 7 9 ∨ Before w true 9 7 :=
  alternatives w true 7 9 mem7 mem9 (by decide)

theorem t318 (w : Witness) : Before w true 7 10 ∨ Before w true 10 7 :=
  alternatives w true 7 10 mem7 mem10 (by decide)

theorem t319 (w : Witness) : Before w true 7 11 ∨ Before w true 11 7 :=
  alternatives w true 7 11 mem7 mem11 (by decide)

theorem t320 (w : Witness) : Before w true 7 12 ∨ Before w true 12 7 :=
  alternatives w true 7 12 mem7 mem12 (by decide)

theorem t321 (w : Witness) : Before w true 7 13 ∨ Before w true 13 7 :=
  alternatives w true 7 13 mem7 mem13 (by decide)

theorem t322 (w : Witness) : Before w true 7 14 ∨ Before w true 14 7 :=
  alternatives w true 7 14 mem7 mem14 (by decide)

theorem t323 (w : Witness) : Before w true 7 15 ∨ Before w true 15 7 :=
  alternatives w true 7 15 mem7 mem15 (by decide)

theorem t324 (w : Witness) : Before w true 7 16 ∨ Before w true 16 7 :=
  alternatives w true 7 16 mem7 mem16 (by decide)

theorem t325 (w : Witness) : Before w true 7 17 ∨ Before w true 17 7 :=
  alternatives w true 7 17 mem7 mem17 (by decide)

theorem t326 (w : Witness) : Before w true 7 18 ∨ Before w true 18 7 :=
  alternatives w true 7 18 mem7 mem18 (by decide)

theorem t327 (w : Witness) : Before w true 7 19 ∨ Before w true 19 7 :=
  alternatives w true 7 19 mem7 mem19 (by decide)

theorem t328 (w : Witness) : Before w true 7 20 ∨ Before w true 20 7 :=
  alternatives w true 7 20 mem7 mem20 (by decide)

theorem t329 (w : Witness) : Before w true 7 21 ∨ Before w true 21 7 :=
  alternatives w true 7 21 mem7 mem21 (by decide)

theorem t330 (w : Witness) : Before w true 8 9 ∨ Before w true 9 8 :=
  alternatives w true 8 9 mem8 mem9 (by decide)

theorem t331 (w : Witness) : Before w true 8 10 ∨ Before w true 10 8 :=
  alternatives w true 8 10 mem8 mem10 (by decide)

theorem t332 (w : Witness) : Before w true 8 11 ∨ Before w true 11 8 :=
  alternatives w true 8 11 mem8 mem11 (by decide)

theorem t333 (w : Witness) : Before w true 8 12 ∨ Before w true 12 8 :=
  alternatives w true 8 12 mem8 mem12 (by decide)

theorem t334 (w : Witness) : Before w true 8 13 ∨ Before w true 13 8 :=
  alternatives w true 8 13 mem8 mem13 (by decide)

theorem t335 (w : Witness) : Before w true 8 14 ∨ Before w true 14 8 :=
  alternatives w true 8 14 mem8 mem14 (by decide)

theorem t336 (w : Witness) : Before w true 8 15 ∨ Before w true 15 8 :=
  alternatives w true 8 15 mem8 mem15 (by decide)

theorem t337 (w : Witness) : Before w true 8 16 ∨ Before w true 16 8 :=
  alternatives w true 8 16 mem8 mem16 (by decide)

theorem t338 (w : Witness) : Before w true 8 17 ∨ Before w true 17 8 :=
  alternatives w true 8 17 mem8 mem17 (by decide)

theorem t339 (w : Witness) : Before w true 8 18 ∨ Before w true 18 8 :=
  alternatives w true 8 18 mem8 mem18 (by decide)

theorem t340 (w : Witness) : Before w true 8 19 ∨ Before w true 19 8 :=
  alternatives w true 8 19 mem8 mem19 (by decide)

theorem t341 (w : Witness) : Before w true 8 20 ∨ Before w true 20 8 :=
  alternatives w true 8 20 mem8 mem20 (by decide)

theorem t342 (w : Witness) : Before w true 8 21 ∨ Before w true 21 8 :=
  alternatives w true 8 21 mem8 mem21 (by decide)

theorem t343 (w : Witness) : Before w true 9 10 ∨ Before w true 10 9 :=
  alternatives w true 9 10 mem9 mem10 (by decide)

theorem t344 (w : Witness) : Before w true 9 11 ∨ Before w true 11 9 :=
  alternatives w true 9 11 mem9 mem11 (by decide)

theorem t345 (w : Witness) : Before w true 9 12 ∨ Before w true 12 9 :=
  alternatives w true 9 12 mem9 mem12 (by decide)

theorem t346 (w : Witness) : Before w true 9 13 ∨ Before w true 13 9 :=
  alternatives w true 9 13 mem9 mem13 (by decide)

theorem t347 (w : Witness) : Before w true 9 14 ∨ Before w true 14 9 :=
  alternatives w true 9 14 mem9 mem14 (by decide)

theorem t348 (w : Witness) : Before w true 9 15 ∨ Before w true 15 9 :=
  alternatives w true 9 15 mem9 mem15 (by decide)

theorem t349 (w : Witness) : Before w true 9 16 ∨ Before w true 16 9 :=
  alternatives w true 9 16 mem9 mem16 (by decide)

theorem t350 (w : Witness) : Before w true 9 17 ∨ Before w true 17 9 :=
  alternatives w true 9 17 mem9 mem17 (by decide)

theorem t351 (w : Witness) : Before w true 9 18 ∨ Before w true 18 9 :=
  alternatives w true 9 18 mem9 mem18 (by decide)

theorem t352 (w : Witness) : Before w true 9 19 ∨ Before w true 19 9 :=
  alternatives w true 9 19 mem9 mem19 (by decide)

theorem t353 (w : Witness) : Before w true 9 20 ∨ Before w true 20 9 :=
  alternatives w true 9 20 mem9 mem20 (by decide)

theorem t354 (w : Witness) : Before w true 9 21 ∨ Before w true 21 9 :=
  alternatives w true 9 21 mem9 mem21 (by decide)

theorem t355 (w : Witness) : Before w true 10 11 ∨ Before w true 11 10 :=
  alternatives w true 10 11 mem10 mem11 (by decide)

theorem t356 (w : Witness) : Before w true 10 12 ∨ Before w true 12 10 :=
  alternatives w true 10 12 mem10 mem12 (by decide)

theorem t357 (w : Witness) : Before w true 10 13 ∨ Before w true 13 10 :=
  alternatives w true 10 13 mem10 mem13 (by decide)

theorem t358 (w : Witness) : Before w true 10 14 ∨ Before w true 14 10 :=
  alternatives w true 10 14 mem10 mem14 (by decide)

theorem t359 (w : Witness) : Before w true 10 15 ∨ Before w true 15 10 :=
  alternatives w true 10 15 mem10 mem15 (by decide)

theorem t360 (w : Witness) : Before w true 10 16 ∨ Before w true 16 10 :=
  alternatives w true 10 16 mem10 mem16 (by decide)

theorem t361 (w : Witness) : Before w true 10 17 ∨ Before w true 17 10 :=
  alternatives w true 10 17 mem10 mem17 (by decide)

theorem t362 (w : Witness) : Before w true 10 18 ∨ Before w true 18 10 :=
  alternatives w true 10 18 mem10 mem18 (by decide)

theorem t363 (w : Witness) : Before w true 10 19 ∨ Before w true 19 10 :=
  alternatives w true 10 19 mem10 mem19 (by decide)

theorem t364 (w : Witness) : Before w true 10 20 ∨ Before w true 20 10 :=
  alternatives w true 10 20 mem10 mem20 (by decide)

theorem t365 (w : Witness) : Before w true 10 21 ∨ Before w true 21 10 :=
  alternatives w true 10 21 mem10 mem21 (by decide)

theorem t366 (w : Witness) : Before w true 11 12 ∨ Before w true 12 11 :=
  alternatives w true 11 12 mem11 mem12 (by decide)

theorem t367 (w : Witness) : Before w true 11 13 ∨ Before w true 13 11 :=
  alternatives w true 11 13 mem11 mem13 (by decide)

theorem t368 (w : Witness) : Before w true 11 14 ∨ Before w true 14 11 :=
  alternatives w true 11 14 mem11 mem14 (by decide)

theorem t369 (w : Witness) : Before w true 11 15 ∨ Before w true 15 11 :=
  alternatives w true 11 15 mem11 mem15 (by decide)

theorem t370 (w : Witness) : Before w true 11 16 ∨ Before w true 16 11 :=
  alternatives w true 11 16 mem11 mem16 (by decide)

theorem t371 (w : Witness) : Before w true 11 17 ∨ Before w true 17 11 :=
  alternatives w true 11 17 mem11 mem17 (by decide)

theorem t372 (w : Witness) : Before w true 11 18 ∨ Before w true 18 11 :=
  alternatives w true 11 18 mem11 mem18 (by decide)

theorem t373 (w : Witness) : Before w true 11 19 ∨ Before w true 19 11 :=
  alternatives w true 11 19 mem11 mem19 (by decide)

theorem t374 (w : Witness) : Before w true 11 20 ∨ Before w true 20 11 :=
  alternatives w true 11 20 mem11 mem20 (by decide)

theorem t375 (w : Witness) : Before w true 11 21 ∨ Before w true 21 11 :=
  alternatives w true 11 21 mem11 mem21 (by decide)

theorem t376 (w : Witness) : Before w true 12 13 ∨ Before w true 13 12 :=
  alternatives w true 12 13 mem12 mem13 (by decide)

theorem t377 (w : Witness) : Before w true 12 14 ∨ Before w true 14 12 :=
  alternatives w true 12 14 mem12 mem14 (by decide)

theorem t378 (w : Witness) : Before w true 12 15 ∨ Before w true 15 12 :=
  alternatives w true 12 15 mem12 mem15 (by decide)

theorem t379 (w : Witness) : Before w true 12 16 ∨ Before w true 16 12 :=
  alternatives w true 12 16 mem12 mem16 (by decide)

theorem t380 (w : Witness) : Before w true 12 17 ∨ Before w true 17 12 :=
  alternatives w true 12 17 mem12 mem17 (by decide)

theorem t381 (w : Witness) : Before w true 12 18 ∨ Before w true 18 12 :=
  alternatives w true 12 18 mem12 mem18 (by decide)

theorem t382 (w : Witness) : Before w true 12 19 ∨ Before w true 19 12 :=
  alternatives w true 12 19 mem12 mem19 (by decide)

theorem t383 (w : Witness) : Before w true 12 20 ∨ Before w true 20 12 :=
  alternatives w true 12 20 mem12 mem20 (by decide)

theorem t384 (w : Witness) : Before w true 12 21 ∨ Before w true 21 12 :=
  alternatives w true 12 21 mem12 mem21 (by decide)

theorem t385 (w : Witness) : Before w true 13 14 ∨ Before w true 14 13 :=
  alternatives w true 13 14 mem13 mem14 (by decide)

theorem t386 (w : Witness) : Before w true 13 15 ∨ Before w true 15 13 :=
  alternatives w true 13 15 mem13 mem15 (by decide)

theorem t387 (w : Witness) : Before w true 13 16 ∨ Before w true 16 13 :=
  alternatives w true 13 16 mem13 mem16 (by decide)

theorem t388 (w : Witness) : Before w true 13 17 ∨ Before w true 17 13 :=
  alternatives w true 13 17 mem13 mem17 (by decide)

theorem t389 (w : Witness) : Before w true 13 18 ∨ Before w true 18 13 :=
  alternatives w true 13 18 mem13 mem18 (by decide)

theorem t390 (w : Witness) : Before w true 13 19 ∨ Before w true 19 13 :=
  alternatives w true 13 19 mem13 mem19 (by decide)

theorem t391 (w : Witness) : Before w true 13 20 ∨ Before w true 20 13 :=
  alternatives w true 13 20 mem13 mem20 (by decide)

theorem t392 (w : Witness) : Before w true 13 21 ∨ Before w true 21 13 :=
  alternatives w true 13 21 mem13 mem21 (by decide)

theorem t393 (w : Witness) : Before w true 14 15 ∨ Before w true 15 14 :=
  alternatives w true 14 15 mem14 mem15 (by decide)

theorem t394 (w : Witness) : Before w true 14 16 ∨ Before w true 16 14 :=
  alternatives w true 14 16 mem14 mem16 (by decide)

theorem t395 (w : Witness) : Before w true 14 17 ∨ Before w true 17 14 :=
  alternatives w true 14 17 mem14 mem17 (by decide)

theorem t396 (w : Witness) : Before w true 14 18 ∨ Before w true 18 14 :=
  alternatives w true 14 18 mem14 mem18 (by decide)

theorem t397 (w : Witness) : Before w true 14 19 ∨ Before w true 19 14 :=
  alternatives w true 14 19 mem14 mem19 (by decide)

theorem t398 (w : Witness) : Before w true 14 20 ∨ Before w true 20 14 :=
  alternatives w true 14 20 mem14 mem20 (by decide)

theorem t399 (w : Witness) : Before w true 14 21 ∨ Before w true 21 14 :=
  alternatives w true 14 21 mem14 mem21 (by decide)

theorem t400 (w : Witness) : Before w true 15 16 ∨ Before w true 16 15 :=
  alternatives w true 15 16 mem15 mem16 (by decide)

theorem t401 (w : Witness) : Before w true 15 17 ∨ Before w true 17 15 :=
  alternatives w true 15 17 mem15 mem17 (by decide)

theorem t402 (w : Witness) : Before w true 15 18 ∨ Before w true 18 15 :=
  alternatives w true 15 18 mem15 mem18 (by decide)

theorem t403 (w : Witness) : Before w true 15 19 ∨ Before w true 19 15 :=
  alternatives w true 15 19 mem15 mem19 (by decide)

theorem t404 (w : Witness) : Before w true 15 20 ∨ Before w true 20 15 :=
  alternatives w true 15 20 mem15 mem20 (by decide)

theorem t405 (w : Witness) : Before w true 15 21 ∨ Before w true 21 15 :=
  alternatives w true 15 21 mem15 mem21 (by decide)

theorem t406 (w : Witness) : Before w true 16 17 ∨ Before w true 17 16 :=
  alternatives w true 16 17 mem16 mem17 (by decide)

theorem t407 (w : Witness) : Before w true 16 18 ∨ Before w true 18 16 :=
  alternatives w true 16 18 mem16 mem18 (by decide)

theorem t408 (w : Witness) : Before w true 16 19 ∨ Before w true 19 16 :=
  alternatives w true 16 19 mem16 mem19 (by decide)

theorem t409 (w : Witness) : Before w true 16 20 ∨ Before w true 20 16 :=
  alternatives w true 16 20 mem16 mem20 (by decide)

theorem t410 (w : Witness) : Before w true 16 21 ∨ Before w true 21 16 :=
  alternatives w true 16 21 mem16 mem21 (by decide)

theorem t411 (w : Witness) : Before w true 17 18 ∨ Before w true 18 17 :=
  alternatives w true 17 18 mem17 mem18 (by decide)

theorem t412 (w : Witness) : Before w true 17 19 ∨ Before w true 19 17 :=
  alternatives w true 17 19 mem17 mem19 (by decide)

theorem t413 (w : Witness) : Before w true 17 20 ∨ Before w true 20 17 :=
  alternatives w true 17 20 mem17 mem20 (by decide)

theorem t414 (w : Witness) : Before w true 17 21 ∨ Before w true 21 17 :=
  alternatives w true 17 21 mem17 mem21 (by decide)

theorem t415 (w : Witness) : Before w true 18 19 ∨ Before w true 19 18 :=
  alternatives w true 18 19 mem18 mem19 (by decide)

theorem t416 (w : Witness) : Before w true 18 20 ∨ Before w true 20 18 :=
  alternatives w true 18 20 mem18 mem20 (by decide)

theorem t417 (w : Witness) : Before w true 18 21 ∨ Before w true 21 18 :=
  alternatives w true 18 21 mem18 mem21 (by decide)

theorem t418 (w : Witness) : Before w true 19 20 ∨ Before w true 20 19 :=
  alternatives w true 19 20 mem19 mem20 (by decide)

theorem t419 (w : Witness) : Before w true 19 21 ∨ Before w true 21 19 :=
  alternatives w true 19 21 mem19 mem21 (by decide)

theorem t420 (w : Witness) : Before w true 20 21 ∨ Before w true 21 20 :=
  alternatives w true 20 21 mem20 mem21 (by decide)


end ThreeStacks.OrderProof
