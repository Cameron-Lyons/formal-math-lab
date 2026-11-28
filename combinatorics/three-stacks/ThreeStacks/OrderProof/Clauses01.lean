import ThreeStacks.CertificateBase

/- Generated natural-deduction proof. See verify/generate_order_proof.py. -/
set_option maxRecDepth 15000
set_option maxHeartbeats 8000000

namespace ThreeStacks.OrderProof

theorem c5283 (w : Witness) : Before w true 18 17 → Before w true 19 18 → Before w true 17 19 → False :=
  fun z0 z1 z2 => cycle w true 18 17 19 z0 z2 z1

theorem c5287 (w : Witness) : Before w true 18 17 → Before w true 20 18 → Before w true 17 20 → False :=
  fun z0 z1 z2 => cycle w true 18 17 20 z0 z2 z1

theorem c5295 (w : Witness) : Before w true 19 17 → Before w true 20 19 → Before w true 17 20 → False :=
  fun z0 z1 z2 => cycle w true 19 17 20 z0 z2 z1

theorem c5297 (w : Witness) : Before w false 19 17 → Before w false 21 19 → Before w false 17 21 → False :=
  fun z0 z1 z2 => cycle w false 19 17 21 z0 z2 z1

theorem c5303 (w : Witness) : Before w true 20 17 → Before w true 21 20 → Before w true 17 21 → False :=
  fun z0 z1 z2 => cycle w true 20 17 21 z0 z2 z1

theorem c5306 (w : Witness) : Before w false 18 19 → Before w false 19 20 → Before w false 20 18 → False :=
  fun z0 z1 z2 => cycle w false 18 19 20 z0 z1 z2

theorem c5307 (w : Witness) : Before w true 19 18 → Before w true 20 19 → Before w true 18 20 → False :=
  fun z0 z1 z2 => cycle w true 19 18 20 z0 z2 z1

theorem c5310 (w : Witness) : Before w false 18 19 → Before w false 19 21 → Before w false 21 18 → False :=
  fun z0 z1 z2 => cycle w false 18 19 21 z0 z1 z2

theorem c5311 (w : Witness) : Before w true 19 18 → Before w true 21 19 → Before w true 18 21 → False :=
  fun z0 z1 z2 => cycle w true 19 18 21 z0 z2 z1

theorem c5314 (w : Witness) : Before w false 18 20 → Before w false 20 21 → Before w false 21 18 → False :=
  fun z0 z1 z2 => cycle w false 18 20 21 z0 z1 z2

theorem c5315 (w : Witness) : Before w true 20 18 → Before w true 21 20 → Before w true 18 21 → False :=
  fun z0 z1 z2 => cycle w true 20 18 21 z0 z2 z1

theorem c5318 (w : Witness) : Before w false 19 20 → Before w false 20 21 → Before w false 21 19 → False :=
  fun z0 z1 z2 => cycle w false 19 20 21 z0 z1 z2

theorem c5319 (w : Witness) : Before w true 20 19 → Before w true 21 20 → Before w true 19 21 → False :=
  fun z0 z1 z2 => cycle w true 20 19 21 z0 z2 z1

theorem c5321 (w : Witness) : Before w false 12 6 → Before w false 6 3 → False :=
  fun z0 z1 => w.entering 6 3 12 (by decide) (by decide) z0 z1

theorem c5322 (w : Witness) : Before w false 8 6 → Before w false 6 3 → False :=
  fun z0 z1 => w.entering 6 3 8 (by decide) (by decide) z0 z1

theorem c5323 (w : Witness) : Before w false 17 6 → Before w false 6 3 → False :=
  fun z0 z1 => w.entering 6 3 17 (by decide) (by decide) z0 z1

theorem c5340 (w : Witness) : Before w false 8 6 → Before w false 6 12 → False :=
  fun z0 z1 => w.entering 6 12 8 (by decide) (by decide) z0 z1

theorem c5341 (w : Witness) : Before w false 17 6 → Before w false 6 12 → False :=
  fun z0 z1 => w.entering 6 12 17 (by decide) (by decide) z0 z1

theorem c5346 (w : Witness) : Before w false 19 6 → Before w false 6 12 → False :=
  fun z0 z1 => w.entering 6 12 19 (by decide) (by decide) z0 z1

theorem c5357 (w : Witness) : Before w false 1 6 → Before w false 6 12 → False :=
  fun z0 z1 => w.entering 6 12 1 (by decide) (by decide) z0 z1

theorem c5358 (w : Witness) : Before w false 17 6 → Before w false 6 8 → False :=
  fun z0 z1 => w.entering 6 8 17 (by decide) (by decide) z0 z1

theorem c5360 (w : Witness) : Before w false 2 6 → Before w false 6 8 → False :=
  fun z0 z1 => w.entering 6 8 2 (by decide) (by decide) z0 z1

theorem c5375 (w : Witness) : Before w false 5 6 → Before w false 6 17 → False :=
  fun z0 z1 => w.entering 6 17 5 (by decide) (by decide) z0 z1

theorem c5377 (w : Witness) : Before w false 11 6 → Before w false 6 17 → False :=
  fun z0 z1 => w.entering 6 17 11 (by decide) (by decide) z0 z1

theorem c5378 (w : Witness) : Before w false 7 6 → Before w false 6 17 → False :=
  fun z0 z1 => w.entering 6 17 7 (by decide) (by decide) z0 z1

theorem c5381 (w : Witness) : Before w false 10 6 → Before w false 6 17 → False :=
  fun z0 z1 => w.entering 6 17 10 (by decide) (by decide) z0 z1

theorem c5391 (w : Witness) : Before w false 2 6 → Before w false 6 5 → False :=
  fun z0 z1 => w.entering 6 5 2 (by decide) (by decide) z0 z1

theorem c5395 (w : Witness) : Before w false 14 6 → Before w false 6 5 → False :=
  fun z0 z1 => w.entering 6 5 14 (by decide) (by decide) z0 z1

theorem c5406 (w : Witness) : Before w false 11 6 → Before w false 6 2 → False :=
  fun z0 z1 => w.entering 6 2 11 (by decide) (by decide) z0 z1

theorem c5409 (w : Witness) : Before w false 14 6 → Before w false 6 2 → False :=
  fun z0 z1 => w.entering 6 2 14 (by decide) (by decide) z0 z1

theorem c5420 (w : Witness) : Before w false 7 6 → Before w false 6 11 → False :=
  fun z0 z1 => w.entering 6 11 7 (by decide) (by decide) z0 z1

theorem c5427 (w : Witness) : Before w false 21 6 → Before w false 6 11 → False :=
  fun z0 z1 => w.entering 6 11 21 (by decide) (by decide) z0 z1

theorem c5433 (w : Witness) : Before w false 19 6 → Before w false 6 7 → False :=
  fun z0 z1 => w.entering 6 7 19 (by decide) (by decide) z0 z1

theorem c5445 (w : Witness) : Before w false 14 6 → Before w false 6 19 → False :=
  fun z0 z1 => w.entering 6 19 14 (by decide) (by decide) z0 z1

theorem c5446 (w : Witness) : Before w false 10 6 → Before w false 6 19 → False :=
  fun z0 z1 => w.entering 6 19 10 (by decide) (by decide) z0 z1

theorem c5447 (w : Witness) : Before w false 4 6 → Before w false 6 19 → False :=
  fun z0 z1 => w.entering 6 19 4 (by decide) (by decide) z0 z1

theorem c5449 (w : Witness) : Before w false 13 6 → Before w false 6 19 → False :=
  fun z0 z1 => w.entering 6 19 13 (by decide) (by decide) z0 z1

theorem c5450 (w : Witness) : Before w false 21 6 → Before w false 6 19 → False :=
  fun z0 z1 => w.entering 6 19 21 (by decide) (by decide) z0 z1

theorem c5457 (w : Witness) : Before w false 4 6 → Before w false 6 14 → False :=
  fun z0 z1 => w.entering 6 14 4 (by decide) (by decide) z0 z1

theorem c5458 (w : Witness) : Before w false 18 6 → Before w false 6 14 → False :=
  fun z0 z1 => w.entering 6 14 18 (by decide) (by decide) z0 z1

theorem c5460 (w : Witness) : Before w false 21 6 → Before w false 6 14 → False :=
  fun z0 z1 => w.entering 6 14 21 (by decide) (by decide) z0 z1

theorem c5463 (w : Witness) : Before w false 20 6 → Before w false 6 14 → False :=
  fun z0 z1 => w.entering 6 14 20 (by decide) (by decide) z0 z1

theorem c5466 (w : Witness) : Before w false 4 6 → Before w false 6 10 → False :=
  fun z0 z1 => w.entering 6 10 4 (by decide) (by decide) z0 z1

theorem c5467 (w : Witness) : Before w false 18 6 → Before w false 6 10 → False :=
  fun z0 z1 => w.entering 6 10 18 (by decide) (by decide) z0 z1

theorem c5468 (w : Witness) : Before w false 13 6 → Before w false 6 10 → False :=
  fun z0 z1 => w.entering 6 10 13 (by decide) (by decide) z0 z1

theorem c5478 (w : Witness) : Before w false 16 6 → Before w false 6 4 → False :=
  fun z0 z1 => w.entering 6 4 16 (by decide) (by decide) z0 z1

theorem c5483 (w : Witness) : Before w false 13 6 → Before w false 6 18 → False :=
  fun z0 z1 => w.entering 6 18 13 (by decide) (by decide) z0 z1

theorem c5484 (w : Witness) : Before w false 21 6 → Before w false 6 18 → False :=
  fun z0 z1 => w.entering 6 18 21 (by decide) (by decide) z0 z1

theorem c5496 (w : Witness) : Before w false 16 6 → Before w false 6 21 → False :=
  fun z0 z1 => w.entering 6 21 16 (by decide) (by decide) z0 z1

theorem c5497 (w : Witness) : Before w false 9 6 → Before w false 6 21 → False :=
  fun z0 z1 => w.entering 6 21 9 (by decide) (by decide) z0 z1

theorem c5498 (w : Witness) : Before w false 20 6 → Before w false 6 21 → False :=
  fun z0 z1 => w.entering 6 21 20 (by decide) (by decide) z0 z1

theorem c5499 (w : Witness) : Before w false 15 6 → Before w false 6 21 → False :=
  fun z0 z1 => w.entering 6 21 15 (by decide) (by decide) z0 z1

theorem c5500 (w : Witness) : Before w false 1 6 → Before w false 6 21 → False :=
  fun z0 z1 => w.entering 6 21 1 (by decide) (by decide) z0 z1

theorem c5501 (w : Witness) : Before w false 9 6 → Before w false 6 16 → False :=
  fun z0 z1 => w.entering 6 16 9 (by decide) (by decide) z0 z1

theorem c5502 (w : Witness) : Before w false 20 6 → Before w false 6 16 → False :=
  fun z0 z1 => w.entering 6 16 20 (by decide) (by decide) z0 z1

theorem c5504 (w : Witness) : Before w false 1 6 → Before w false 6 16 → False :=
  fun z0 z1 => w.entering 6 16 1 (by decide) (by decide) z0 z1

theorem c5506 (w : Witness) : Before w false 15 6 → Before w false 6 9 → False :=
  fun z0 z1 => w.entering 6 9 15 (by decide) (by decide) z0 z1

theorem c5509 (w : Witness) : Before w false 1 6 → Before w false 6 20 → False :=
  fun z0 z1 => w.entering 6 20 1 (by decide) (by decide) z0 z1

theorem c5511 (w : Witness) : Before w false 8 3 → Before w false 3 12 → False :=
  fun z0 z1 => w.entering 3 12 8 (by decide) (by decide) z0 z1

theorem c5512 (w : Witness) : Before w false 17 3 → Before w false 3 12 → False :=
  fun z0 z1 => w.entering 3 12 17 (by decide) (by decide) z0 z1

theorem c5513 (w : Witness) : Before w false 5 3 → Before w false 3 12 → False :=
  fun z0 z1 => w.entering 3 12 5 (by decide) (by decide) z0 z1

theorem c5514 (w : Witness) : Before w false 2 3 → Before w false 3 12 → False :=
  fun z0 z1 => w.entering 3 12 2 (by decide) (by decide) z0 z1

theorem c5529 (w : Witness) : Before w false 17 3 → Before w false 3 8 → False :=
  fun z0 z1 => w.entering 3 8 17 (by decide) (by decide) z0 z1

theorem c5530 (w : Witness) : Before w false 5 3 → Before w false 3 8 → False :=
  fun z0 z1 => w.entering 3 8 5 (by decide) (by decide) z0 z1

theorem c5547 (w : Witness) : Before w false 2 3 → Before w false 3 17 → False :=
  fun z0 z1 => w.entering 3 17 2 (by decide) (by decide) z0 z1

theorem c5554 (w : Witness) : Before w false 18 3 → Before w false 3 17 → False :=
  fun z0 z1 => w.entering 3 17 18 (by decide) (by decide) z0 z1

theorem c5556 (w : Witness) : Before w false 21 3 → Before w false 3 17 → False :=
  fun z0 z1 => w.entering 3 17 21 (by decide) (by decide) z0 z1

theorem c5562 (w : Witness) : Before w false 2 3 → Before w false 3 5 → False :=
  fun z0 z1 => w.entering 3 5 2 (by decide) (by decide) z0 z1

theorem c5577 (w : Witness) : Before w false 11 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 11 (by decide) (by decide) z0 z1

theorem c5578 (w : Witness) : Before w false 7 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 7 (by decide) (by decide) z0 z1

theorem c5579 (w : Witness) : Before w false 19 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 19 (by decide) (by decide) z0 z1

theorem c5580 (w : Witness) : Before w false 14 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 14 (by decide) (by decide) z0 z1

theorem c5581 (w : Witness) : Before w false 10 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 10 (by decide) (by decide) z0 z1

theorem c5582 (w : Witness) : Before w false 4 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 4 (by decide) (by decide) z0 z1

theorem c5583 (w : Witness) : Before w false 18 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 18 (by decide) (by decide) z0 z1

theorem c5584 (w : Witness) : Before w false 13 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 13 (by decide) (by decide) z0 z1

theorem c5585 (w : Witness) : Before w false 21 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 21 (by decide) (by decide) z0 z1

theorem c5586 (w : Witness) : Before w false 16 3 → Before w false 3 2 → False :=
  fun z0 z1 => w.entering 3 2 16 (by decide) (by decide) z0 z1

theorem c5591 (w : Witness) : Before w false 7 3 → Before w false 3 11 → False :=
  fun z0 z1 => w.entering 3 11 7 (by decide) (by decide) z0 z1

theorem c5592 (w : Witness) : Before w false 19 3 → Before w false 3 11 → False :=
  fun z0 z1 => w.entering 3 11 19 (by decide) (by decide) z0 z1

theorem c5597 (w : Witness) : Before w false 13 3 → Before w false 3 11 → False :=
  fun z0 z1 => w.entering 3 11 13 (by decide) (by decide) z0 z1

theorem c5604 (w : Witness) : Before w false 19 3 → Before w false 3 7 → False :=
  fun z0 z1 => w.entering 3 7 19 (by decide) (by decide) z0 z1

theorem c5616 (w : Witness) : Before w false 14 3 → Before w false 3 19 → False :=
  fun z0 z1 => w.entering 3 19 14 (by decide) (by decide) z0 z1

theorem c5617 (w : Witness) : Before w false 10 3 → Before w false 3 19 → False :=
  fun z0 z1 => w.entering 3 19 10 (by decide) (by decide) z0 z1

theorem c5620 (w : Witness) : Before w false 13 3 → Before w false 3 19 → False :=
  fun z0 z1 => w.entering 3 19 13 (by decide) (by decide) z0 z1

theorem c5627 (w : Witness) : Before w false 10 3 → Before w false 3 14 → False :=
  fun z0 z1 => w.entering 3 14 10 (by decide) (by decide) z0 z1

theorem c5633 (w : Witness) : Before w false 9 3 → Before w false 3 14 → False :=
  fun z0 z1 => w.entering 3 14 9 (by decide) (by decide) z0 z1

theorem c5637 (w : Witness) : Before w false 4 3 → Before w false 3 10 → False :=
  fun z0 z1 => w.entering 3 10 4 (by decide) (by decide) z0 z1

theorem c5639 (w : Witness) : Before w false 13 3 → Before w false 3 10 → False :=
  fun z0 z1 => w.entering 3 10 13 (by decide) (by decide) z0 z1

theorem c5646 (w : Witness) : Before w false 18 3 → Before w false 3 4 → False :=
  fun z0 z1 => w.entering 3 4 18 (by decide) (by decide) z0 z1

theorem c5654 (w : Witness) : Before w false 13 3 → Before w false 3 18 → False :=
  fun z0 z1 => w.entering 3 18 13 (by decide) (by decide) z0 z1

theorem c5655 (w : Witness) : Before w false 21 3 → Before w false 3 18 → False :=
  fun z0 z1 => w.entering 3 18 21 (by decide) (by decide) z0 z1

theorem c5661 (w : Witness) : Before w false 21 3 → Before w false 3 13 → False :=
  fun z0 z1 => w.entering 3 13 21 (by decide) (by decide) z0 z1

theorem c5667 (w : Witness) : Before w false 16 3 → Before w false 3 21 → False :=
  fun z0 z1 => w.entering 3 21 16 (by decide) (by decide) z0 z1

theorem c5668 (w : Witness) : Before w false 9 3 → Before w false 3 21 → False :=
  fun z0 z1 => w.entering 3 21 9 (by decide) (by decide) z0 z1

theorem c5669 (w : Witness) : Before w false 20 3 → Before w false 3 21 → False :=
  fun z0 z1 => w.entering 3 21 20 (by decide) (by decide) z0 z1

theorem c5670 (w : Witness) : Before w false 15 3 → Before w false 3 21 → False :=
  fun z0 z1 => w.entering 3 21 15 (by decide) (by decide) z0 z1

theorem c5671 (w : Witness) : Before w false 1 3 → Before w false 3 21 → False :=
  fun z0 z1 => w.entering 3 21 1 (by decide) (by decide) z0 z1

theorem c5672 (w : Witness) : Before w false 9 3 → Before w false 3 16 → False :=
  fun z0 z1 => w.entering 3 16 9 (by decide) (by decide) z0 z1

theorem c5676 (w : Witness) : Before w false 20 3 → Before w false 3 9 → False :=
  fun z0 z1 => w.entering 3 9 20 (by decide) (by decide) z0 z1

theorem c5677 (w : Witness) : Before w false 15 3 → Before w false 3 9 → False :=
  fun z0 z1 => w.entering 3 9 15 (by decide) (by decide) z0 z1

theorem c5678 (w : Witness) : Before w false 1 3 → Before w false 3 9 → False :=
  fun z0 z1 => w.entering 3 9 1 (by decide) (by decide) z0 z1

theorem c5679 (w : Witness) : Before w false 15 3 → Before w false 3 20 → False :=
  fun z0 z1 => w.entering 3 20 15 (by decide) (by decide) z0 z1

theorem c5680 (w : Witness) : Before w false 1 3 → Before w false 3 20 → False :=
  fun z0 z1 => w.entering 3 20 1 (by decide) (by decide) z0 z1

theorem c5682 (w : Witness) : Before w false 17 12 → Before w false 12 8 → False :=
  fun z0 z1 => w.entering 12 8 17 (by decide) (by decide) z0 z1

theorem c5683 (w : Witness) : Before w false 5 12 → Before w false 12 8 → False :=
  fun z0 z1 => w.entering 12 8 5 (by decide) (by decide) z0 z1

theorem c5685 (w : Witness) : Before w false 11 12 → Before w false 12 8 → False :=
  fun z0 z1 => w.entering 12 8 11 (by decide) (by decide) z0 z1

theorem c5687 (w : Witness) : Before w false 19 12 → Before w false 12 8 → False :=
  fun z0 z1 => w.entering 12 8 19 (by decide) (by decide) z0 z1

theorem c5691 (w : Witness) : Before w false 18 12 → Before w false 12 8 → False :=
  fun z0 z1 => w.entering 12 8 18 (by decide) (by decide) z0 z1

theorem c5699 (w : Witness) : Before w false 5 12 → Before w false 12 17 → False :=
  fun z0 z1 => w.entering 12 17 5 (by decide) (by decide) z0 z1

theorem c5700 (w : Witness) : Before w false 2 12 → Before w false 12 17 → False :=
  fun z0 z1 => w.entering 12 17 2 (by decide) (by decide) z0 z1

theorem c5701 (w : Witness) : Before w false 11 12 → Before w false 12 17 → False :=
  fun z0 z1 => w.entering 12 17 11 (by decide) (by decide) z0 z1

theorem c5708 (w : Witness) : Before w false 13 12 → Before w false 12 17 → False :=
  fun z0 z1 => w.entering 12 17 13 (by decide) (by decide) z0 z1

theorem c5709 (w : Witness) : Before w false 21 12 → Before w false 12 17 → False :=
  fun z0 z1 => w.entering 12 17 21 (by decide) (by decide) z0 z1

theorem c5715 (w : Witness) : Before w false 2 12 → Before w false 12 5 → False :=
  fun z0 z1 => w.entering 12 5 2 (by decide) (by decide) z0 z1

theorem c5720 (w : Witness) : Before w false 10 12 → Before w false 12 5 → False :=
  fun z0 z1 => w.entering 12 5 10 (by decide) (by decide) z0 z1

theorem c5730 (w : Witness) : Before w false 11 12 → Before w false 12 2 → False :=
  fun z0 z1 => w.entering 12 2 11 (by decide) (by decide) z0 z1

theorem c5731 (w : Witness) : Before w false 7 12 → Before w false 12 2 → False :=
  fun z0 z1 => w.entering 12 2 7 (by decide) (by decide) z0 z1

theorem c5736 (w : Witness) : Before w false 18 12 → Before w false 12 2 → False :=
  fun z0 z1 => w.entering 12 2 18 (by decide) (by decide) z0 z1

theorem c5744 (w : Witness) : Before w false 7 12 → Before w false 12 11 → False :=
  fun z0 z1 => w.entering 12 11 7 (by decide) (by decide) z0 z1

theorem c5745 (w : Witness) : Before w false 19 12 → Before w false 12 11 → False :=
  fun z0 z1 => w.entering 12 11 19 (by decide) (by decide) z0 z1

theorem c5757 (w : Witness) : Before w false 19 12 → Before w false 12 7 → False :=
  fun z0 z1 => w.entering 12 7 19 (by decide) (by decide) z0 z1

theorem c5761 (w : Witness) : Before w false 18 12 → Before w false 12 7 → False :=
  fun z0 z1 => w.entering 12 7 18 (by decide) (by decide) z0 z1

theorem c5769 (w : Witness) : Before w false 14 12 → Before w false 12 19 → False :=
  fun z0 z1 => w.entering 12 19 14 (by decide) (by decide) z0 z1

theorem c5770 (w : Witness) : Before w false 10 12 → Before w false 12 19 → False :=
  fun z0 z1 => w.entering 12 19 10 (by decide) (by decide) z0 z1

theorem c5771 (w : Witness) : Before w false 4 12 → Before w false 12 19 → False :=
  fun z0 z1 => w.entering 12 19 4 (by decide) (by decide) z0 z1

theorem c5772 (w : Witness) : Before w false 18 12 → Before w false 12 19 → False :=
  fun z0 z1 => w.entering 12 19 18 (by decide) (by decide) z0 z1

theorem c5773 (w : Witness) : Before w false 13 12 → Before w false 12 19 → False :=
  fun z0 z1 => w.entering 12 19 13 (by decide) (by decide) z0 z1

theorem c5774 (w : Witness) : Before w false 21 12 → Before w false 12 19 → False :=
  fun z0 z1 => w.entering 12 19 21 (by decide) (by decide) z0 z1

theorem c5780 (w : Witness) : Before w false 10 12 → Before w false 12 14 → False :=
  fun z0 z1 => w.entering 12 14 10 (by decide) (by decide) z0 z1

theorem c5782 (w : Witness) : Before w false 18 12 → Before w false 12 14 → False :=
  fun z0 z1 => w.entering 12 14 18 (by decide) (by decide) z0 z1

theorem c5790 (w : Witness) : Before w false 4 12 → Before w false 12 10 → False :=
  fun z0 z1 => w.entering 12 10 4 (by decide) (by decide) z0 z1

theorem c5791 (w : Witness) : Before w false 18 12 → Before w false 12 10 → False :=
  fun z0 z1 => w.entering 12 10 18 (by decide) (by decide) z0 z1

theorem c5793 (w : Witness) : Before w false 21 12 → Before w false 12 10 → False :=
  fun z0 z1 => w.entering 12 10 21 (by decide) (by decide) z0 z1

theorem c5795 (w : Witness) : Before w false 9 12 → Before w false 12 10 → False :=
  fun z0 z1 => w.entering 12 10 9 (by decide) (by decide) z0 z1

theorem c5796 (w : Witness) : Before w false 20 12 → Before w false 12 10 → False :=
  fun z0 z1 => w.entering 12 10 20 (by decide) (by decide) z0 z1

theorem c5799 (w : Witness) : Before w false 18 12 → Before w false 12 4 → False :=
  fun z0 z1 => w.entering 12 4 18 (by decide) (by decide) z0 z1

theorem c5801 (w : Witness) : Before w false 21 12 → Before w false 12 4 → False :=
  fun z0 z1 => w.entering 12 4 21 (by decide) (by decide) z0 z1

theorem c5807 (w : Witness) : Before w false 13 12 → Before w false 12 18 → False :=
  fun z0 z1 => w.entering 12 18 13 (by decide) (by decide) z0 z1

theorem c5808 (w : Witness) : Before w false 21 12 → Before w false 12 18 → False :=
  fun z0 z1 => w.entering 12 18 21 (by decide) (by decide) z0 z1

theorem c5814 (w : Witness) : Before w false 21 12 → Before w false 12 13 → False :=
  fun z0 z1 => w.entering 12 13 21 (by decide) (by decide) z0 z1

theorem c5820 (w : Witness) : Before w false 16 12 → Before w false 12 21 → False :=
  fun z0 z1 => w.entering 12 21 16 (by decide) (by decide) z0 z1

theorem c5821 (w : Witness) : Before w false 9 12 → Before w false 12 21 → False :=
  fun z0 z1 => w.entering 12 21 9 (by decide) (by decide) z0 z1

theorem c5822 (w : Witness) : Before w false 20 12 → Before w false 12 21 → False :=
  fun z0 z1 => w.entering 12 21 20 (by decide) (by decide) z0 z1

theorem c5823 (w : Witness) : Before w false 15 12 → Before w false 12 21 → False :=
  fun z0 z1 => w.entering 12 21 15 (by decide) (by decide) z0 z1

theorem c5824 (w : Witness) : Before w false 1 12 → Before w false 12 21 → False :=
  fun z0 z1 => w.entering 12 21 1 (by decide) (by decide) z0 z1

theorem c5826 (w : Witness) : Before w false 20 12 → Before w false 12 16 → False :=
  fun z0 z1 => w.entering 12 16 20 (by decide) (by decide) z0 z1

theorem c5828 (w : Witness) : Before w false 1 12 → Before w false 12 16 → False :=
  fun z0 z1 => w.entering 12 16 1 (by decide) (by decide) z0 z1

theorem c5829 (w : Witness) : Before w false 20 12 → Before w false 12 9 → False :=
  fun z0 z1 => w.entering 12 9 20 (by decide) (by decide) z0 z1

theorem c5831 (w : Witness) : Before w false 1 12 → Before w false 12 9 → False :=
  fun z0 z1 => w.entering 12 9 1 (by decide) (by decide) z0 z1

theorem c5832 (w : Witness) : Before w false 15 12 → Before w false 12 20 → False :=
  fun z0 z1 => w.entering 12 20 15 (by decide) (by decide) z0 z1

theorem c5833 (w : Witness) : Before w false 1 12 → Before w false 12 20 → False :=
  fun z0 z1 => w.entering 12 20 1 (by decide) (by decide) z0 z1

theorem c5834 (w : Witness) : Before w false 1 12 → Before w false 12 15 → False :=
  fun z0 z1 => w.entering 12 15 1 (by decide) (by decide) z0 z1

theorem c5835 (w : Witness) : Before w false 5 8 → Before w false 8 17 → False :=
  fun z0 z1 => w.entering 8 17 5 (by decide) (by decide) z0 z1

theorem c5836 (w : Witness) : Before w false 2 8 → Before w false 8 17 → False :=
  fun z0 z1 => w.entering 8 17 2 (by decide) (by decide) z0 z1

theorem c5838 (w : Witness) : Before w false 7 8 → Before w false 8 17 → False :=
  fun z0 z1 => w.entering 8 17 7 (by decide) (by decide) z0 z1

theorem c5839 (w : Witness) : Before w false 19 8 → Before w false 8 17 → False :=
  fun z0 z1 => w.entering 8 17 19 (by decide) (by decide) z0 z1

theorem c5840 (w : Witness) : Before w false 14 8 → Before w false 8 17 → False :=
  fun z0 z1 => w.entering 8 17 14 (by decide) (by decide) z0 z1

theorem c5844 (w : Witness) : Before w false 13 8 → Before w false 8 17 → False :=
  fun z0 z1 => w.entering 8 17 13 (by decide) (by decide) z0 z1

theorem c5845 (w : Witness) : Before w false 21 8 → Before w false 8 17 → False :=
  fun z0 z1 => w.entering 8 17 21 (by decide) (by decide) z0 z1

theorem c5851 (w : Witness) : Before w false 2 8 → Before w false 8 5 → False :=
  fun z0 z1 => w.entering 8 5 2 (by decide) (by decide) z0 z1

theorem c5852 (w : Witness) : Before w false 11 8 → Before w false 8 5 → False :=
  fun z0 z1 => w.entering 8 5 11 (by decide) (by decide) z0 z1

theorem c5853 (w : Witness) : Before w false 7 8 → Before w false 8 5 → False :=
  fun z0 z1 => w.entering 8 5 7 (by decide) (by decide) z0 z1

theorem c5866 (w : Witness) : Before w false 11 8 → Before w false 8 2 → False :=
  fun z0 z1 => w.entering 8 2 11 (by decide) (by decide) z0 z1

theorem c5867 (w : Witness) : Before w false 7 8 → Before w false 8 2 → False :=
  fun z0 z1 => w.entering 8 2 7 (by decide) (by decide) z0 z1

theorem c5880 (w : Witness) : Before w false 7 8 → Before w false 8 11 → False :=
  fun z0 z1 => w.entering 8 11 7 (by decide) (by decide) z0 z1

theorem c5893 (w : Witness) : Before w false 19 8 → Before w false 8 7 → False :=
  fun z0 z1 => w.entering 8 7 19 (by decide) (by decide) z0 z1

theorem c5894 (w : Witness) : Before w false 14 8 → Before w false 8 7 → False :=
  fun z0 z1 => w.entering 8 7 14 (by decide) (by decide) z0 z1

theorem c5896 (w : Witness) : Before w false 4 8 → Before w false 8 7 → False :=
  fun z0 z1 => w.entering 8 7 4 (by decide) (by decide) z0 z1

theorem c5897 (w : Witness) : Before w false 18 8 → Before w false 8 7 → False :=
  fun z0 z1 => w.entering 8 7 18 (by decide) (by decide) z0 z1

theorem c5899 (w : Witness) : Before w false 21 8 → Before w false 8 7 → False :=
  fun z0 z1 => w.entering 8 7 21 (by decide) (by decide) z0 z1

theorem c5905 (w : Witness) : Before w false 14 8 → Before w false 8 19 → False :=
  fun z0 z1 => w.entering 8 19 14 (by decide) (by decide) z0 z1

theorem c5906 (w : Witness) : Before w false 10 8 → Before w false 8 19 → False :=
  fun z0 z1 => w.entering 8 19 10 (by decide) (by decide) z0 z1

theorem c5907 (w : Witness) : Before w false 4 8 → Before w false 8 19 → False :=
  fun z0 z1 => w.entering 8 19 4 (by decide) (by decide) z0 z1

theorem c5908 (w : Witness) : Before w false 18 8 → Before w false 8 19 → False :=
  fun z0 z1 => w.entering 8 19 18 (by decide) (by decide) z0 z1

theorem c5909 (w : Witness) : Before w false 13 8 → Before w false 8 19 → False :=
  fun z0 z1 => w.entering 8 19 13 (by decide) (by decide) z0 z1

theorem c5910 (w : Witness) : Before w false 21 8 → Before w false 8 19 → False :=
  fun z0 z1 => w.entering 8 19 21 (by decide) (by decide) z0 z1

theorem c5916 (w : Witness) : Before w false 10 8 → Before w false 8 14 → False :=
  fun z0 z1 => w.entering 8 14 10 (by decide) (by decide) z0 z1

theorem c5917 (w : Witness) : Before w false 4 8 → Before w false 8 14 → False :=
  fun z0 z1 => w.entering 8 14 4 (by decide) (by decide) z0 z1

theorem c5926 (w : Witness) : Before w false 4 8 → Before w false 8 10 → False :=
  fun z0 z1 => w.entering 8 10 4 (by decide) (by decide) z0 z1

theorem c5927 (w : Witness) : Before w false 18 8 → Before w false 8 10 → False :=
  fun z0 z1 => w.entering 8 10 18 (by decide) (by decide) z0 z1

theorem c5929 (w : Witness) : Before w false 21 8 → Before w false 8 10 → False :=
  fun z0 z1 => w.entering 8 10 21 (by decide) (by decide) z0 z1

theorem c5935 (w : Witness) : Before w false 18 8 → Before w false 8 4 → False :=
  fun z0 z1 => w.entering 8 4 18 (by decide) (by decide) z0 z1

theorem c5936 (w : Witness) : Before w false 13 8 → Before w false 8 4 → False :=
  fun z0 z1 => w.entering 8 4 13 (by decide) (by decide) z0 z1

theorem c5943 (w : Witness) : Before w false 13 8 → Before w false 8 18 → False :=
  fun z0 z1 => w.entering 8 18 13 (by decide) (by decide) z0 z1

theorem c5944 (w : Witness) : Before w false 21 8 → Before w false 8 18 → False :=
  fun z0 z1 => w.entering 8 18 21 (by decide) (by decide) z0 z1

theorem c5956 (w : Witness) : Before w false 16 8 → Before w false 8 21 → False :=
  fun z0 z1 => w.entering 8 21 16 (by decide) (by decide) z0 z1

theorem c5957 (w : Witness) : Before w false 9 8 → Before w false 8 21 → False :=
  fun z0 z1 => w.entering 8 21 9 (by decide) (by decide) z0 z1

theorem c5958 (w : Witness) : Before w false 20 8 → Before w false 8 21 → False :=
  fun z0 z1 => w.entering 8 21 20 (by decide) (by decide) z0 z1

theorem c5959 (w : Witness) : Before w false 15 8 → Before w false 8 21 → False :=
  fun z0 z1 => w.entering 8 21 15 (by decide) (by decide) z0 z1

theorem c5960 (w : Witness) : Before w false 1 8 → Before w false 8 21 → False :=
  fun z0 z1 => w.entering 8 21 1 (by decide) (by decide) z0 z1

theorem c5962 (w : Witness) : Before w false 20 8 → Before w false 8 16 → False :=
  fun z0 z1 => w.entering 8 16 20 (by decide) (by decide) z0 z1

theorem c5965 (w : Witness) : Before w false 20 8 → Before w false 8 9 → False :=
  fun z0 z1 => w.entering 8 9 20 (by decide) (by decide) z0 z1

theorem c5969 (w : Witness) : Before w false 1 8 → Before w false 8 20 → False :=
  fun z0 z1 => w.entering 8 20 1 (by decide) (by decide) z0 z1

theorem c5972 (w : Witness) : Before w false 11 17 → Before w false 17 5 → False :=
  fun z0 z1 => w.entering 17 5 11 (by decide) (by decide) z0 z1

theorem c5973 (w : Witness) : Before w false 7 17 → Before w false 17 5 → False :=
  fun z0 z1 => w.entering 17 5 7 (by decide) (by decide) z0 z1

theorem c5986 (w : Witness) : Before w false 11 17 → Before w false 17 2 → False :=
  fun z0 z1 => w.entering 17 2 11 (by decide) (by decide) z0 z1

theorem c6000 (w : Witness) : Before w false 7 17 → Before w false 17 11 → False :=
  fun z0 z1 => w.entering 17 11 7 (by decide) (by decide) z0 z1

theorem c6005 (w : Witness) : Before w false 18 17 → Before w false 17 11 → False :=
  fun z0 z1 => w.entering 17 11 18 (by decide) (by decide) z0 z1

theorem c6007 (w : Witness) : Before w false 21 17 → Before w false 17 11 → False :=
  fun z0 z1 => w.entering 17 11 21 (by decide) (by decide) z0 z1

theorem c6013 (w : Witness) : Before w false 19 17 → Before w false 17 7 → False :=
  fun z0 z1 => w.entering 17 7 19 (by decide) (by decide) z0 z1

theorem c6014 (w : Witness) : Before w false 14 17 → Before w false 17 7 → False :=
  fun z0 z1 => w.entering 17 7 14 (by decide) (by decide) z0 z1

theorem c6015 (w : Witness) : Before w false 10 17 → Before w false 17 7 → False :=
  fun z0 z1 => w.entering 17 7 10 (by decide) (by decide) z0 z1

theorem c6016 (w : Witness) : Before w false 4 17 → Before w false 17 7 → False :=
  fun z0 z1 => w.entering 17 7 4 (by decide) (by decide) z0 z1

theorem c6020 (w : Witness) : Before w false 16 17 → Before w false 17 7 → False :=
  fun z0 z1 => w.entering 17 7 16 (by decide) (by decide) z0 z1

theorem c6025 (w : Witness) : Before w false 14 17 → Before w false 17 19 → False :=
  fun z0 z1 => w.entering 17 19 14 (by decide) (by decide) z0 z1

theorem c6026 (w : Witness) : Before w false 10 17 → Before w false 17 19 → False :=
  fun z0 z1 => w.entering 17 19 10 (by decide) (by decide) z0 z1

theorem c6028 (w : Witness) : Before w false 18 17 → Before w false 17 19 → False :=
  fun z0 z1 => w.entering 17 19 18 (by decide) (by decide) z0 z1

theorem c6030 (w : Witness) : Before w false 21 17 → Before w false 17 19 → False :=
  fun z0 z1 => w.entering 17 19 21 (by decide) (by decide) z0 z1

theorem c6033 (w : Witness) : Before w false 20 17 → Before w false 17 19 → False :=
  fun z0 z1 => w.entering 17 19 20 (by decide) (by decide) z0 z1

theorem c6036 (w : Witness) : Before w false 10 17 → Before w false 17 14 → False :=
  fun z0 z1 => w.entering 17 14 10 (by decide) (by decide) z0 z1

theorem c6040 (w : Witness) : Before w false 21 17 → Before w false 17 14 → False :=
  fun z0 z1 => w.entering 17 14 21 (by decide) (by decide) z0 z1

theorem c6046 (w : Witness) : Before w false 4 17 → Before w false 17 10 → False :=
  fun z0 z1 => w.entering 17 10 4 (by decide) (by decide) z0 z1

theorem c6048 (w : Witness) : Before w false 13 17 → Before w false 17 10 → False :=
  fun z0 z1 => w.entering 17 10 13 (by decide) (by decide) z0 z1

theorem c6050 (w : Witness) : Before w false 16 17 → Before w false 17 10 → False :=
  fun z0 z1 => w.entering 17 10 16 (by decide) (by decide) z0 z1

theorem c6052 (w : Witness) : Before w false 20 17 → Before w false 17 10 → False :=
  fun z0 z1 => w.entering 17 10 20 (by decide) (by decide) z0 z1

theorem c6057 (w : Witness) : Before w false 21 17 → Before w false 17 4 → False :=
  fun z0 z1 => w.entering 17 4 21 (by decide) (by decide) z0 z1

theorem c6061 (w : Witness) : Before w false 15 17 → Before w false 17 4 → False :=
  fun z0 z1 => w.entering 17 4 15 (by decide) (by decide) z0 z1

theorem c6063 (w : Witness) : Before w false 13 17 → Before w false 17 18 → False :=
  fun z0 z1 => w.entering 17 18 13 (by decide) (by decide) z0 z1

theorem c6064 (w : Witness) : Before w false 21 17 → Before w false 17 18 → False :=
  fun z0 z1 => w.entering 17 18 21 (by decide) (by decide) z0 z1

theorem c6070 (w : Witness) : Before w false 21 17 → Before w false 17 13 → False :=
  fun z0 z1 => w.entering 17 13 21 (by decide) (by decide) z0 z1

theorem c6075 (w : Witness) : Before w false 1 17 → Before w false 17 13 → False :=
  fun z0 z1 => w.entering 17 13 1 (by decide) (by decide) z0 z1

theorem c6076 (w : Witness) : Before w false 16 17 → Before w false 17 21 → False :=
  fun z0 z1 => w.entering 17 21 16 (by decide) (by decide) z0 z1

theorem c6077 (w : Witness) : Before w false 9 17 → Before w false 17 21 → False :=
  fun z0 z1 => w.entering 17 21 9 (by decide) (by decide) z0 z1

theorem c6080 (w : Witness) : Before w false 1 17 → Before w false 17 21 → False :=
  fun z0 z1 => w.entering 17 21 1 (by decide) (by decide) z0 z1

theorem c6082 (w : Witness) : Before w false 20 17 → Before w false 17 16 → False :=
  fun z0 z1 => w.entering 17 16 20 (by decide) (by decide) z0 z1

theorem c6085 (w : Witness) : Before w false 20 17 → Before w false 17 9 → False :=
  fun z0 z1 => w.entering 17 9 20 (by decide) (by decide) z0 z1

theorem c6088 (w : Witness) : Before w false 15 17 → Before w false 17 20 → False :=
  fun z0 z1 => w.entering 17 20 15 (by decide) (by decide) z0 z1

theorem c6089 (w : Witness) : Before w false 1 17 → Before w false 17 20 → False :=
  fun z0 z1 => w.entering 17 20 1 (by decide) (by decide) z0 z1

theorem c6090 (w : Witness) : Before w false 1 17 → Before w false 17 15 → False :=
  fun z0 z1 => w.entering 17 15 1 (by decide) (by decide) z0 z1

theorem c6091 (w : Witness) : Before w false 11 5 → Before w false 5 2 → False :=
  fun z0 z1 => w.entering 5 2 11 (by decide) (by decide) z0 z1

theorem c6092 (w : Witness) : Before w false 7 5 → Before w false 5 2 → False :=
  fun z0 z1 => w.entering 5 2 7 (by decide) (by decide) z0 z1

theorem c6093 (w : Witness) : Before w false 19 5 → Before w false 5 2 → False :=
  fun z0 z1 => w.entering 5 2 19 (by decide) (by decide) z0 z1

theorem c6097 (w : Witness) : Before w false 18 5 → Before w false 5 2 → False :=
  fun z0 z1 => w.entering 5 2 18 (by decide) (by decide) z0 z1

theorem c6105 (w : Witness) : Before w false 7 5 → Before w false 5 11 → False :=
  fun z0 z1 => w.entering 5 11 7 (by decide) (by decide) z0 z1

theorem c6106 (w : Witness) : Before w false 19 5 → Before w false 5 11 → False :=
  fun z0 z1 => w.entering 5 11 19 (by decide) (by decide) z0 z1

theorem c6107 (w : Witness) : Before w false 14 5 → Before w false 5 11 → False :=
  fun z0 z1 => w.entering 5 11 14 (by decide) (by decide) z0 z1

theorem c6108 (w : Witness) : Before w false 10 5 → Before w false 5 11 → False :=
  fun z0 z1 => w.entering 5 11 10 (by decide) (by decide) z0 z1

theorem c6118 (w : Witness) : Before w false 19 5 → Before w false 5 7 → False :=
  fun z0 z1 => w.entering 5 7 19 (by decide) (by decide) z0 z1

theorem c6121 (w : Witness) : Before w false 4 5 → Before w false 5 7 → False :=
  fun z0 z1 => w.entering 5 7 4 (by decide) (by decide) z0 z1

theorem c6130 (w : Witness) : Before w false 14 5 → Before w false 5 19 → False :=
  fun z0 z1 => w.entering 5 19 14 (by decide) (by decide) z0 z1

theorem c6131 (w : Witness) : Before w false 10 5 → Before w false 5 19 → False :=
  fun z0 z1 => w.entering 5 19 10 (by decide) (by decide) z0 z1

theorem c6133 (w : Witness) : Before w false 18 5 → Before w false 5 19 → False :=
  fun z0 z1 => w.entering 5 19 18 (by decide) (by decide) z0 z1

theorem c6135 (w : Witness) : Before w false 21 5 → Before w false 5 19 → False :=
  fun z0 z1 => w.entering 5 19 21 (by decide) (by decide) z0 z1

theorem c6141 (w : Witness) : Before w false 10 5 → Before w false 5 14 → False :=
  fun z0 z1 => w.entering 5 14 10 (by decide) (by decide) z0 z1

theorem c6142 (w : Witness) : Before w false 4 5 → Before w false 5 14 → False :=
  fun z0 z1 => w.entering 5 14 4 (by decide) (by decide) z0 z1

theorem c6143 (w : Witness) : Before w false 18 5 → Before w false 5 14 → False :=
  fun z0 z1 => w.entering 5 14 18 (by decide) (by decide) z0 z1

theorem c6145 (w : Witness) : Before w false 21 5 → Before w false 5 14 → False :=
  fun z0 z1 => w.entering 5 14 21 (by decide) (by decide) z0 z1

theorem c6155 (w : Witness) : Before w false 16 5 → Before w false 5 10 → False :=
  fun z0 z1 => w.entering 5 10 16 (by decide) (by decide) z0 z1

theorem c6168 (w : Witness) : Before w false 13 5 → Before w false 5 18 → False :=
  fun z0 z1 => w.entering 5 18 13 (by decide) (by decide) z0 z1

theorem c6169 (w : Witness) : Before w false 21 5 → Before w false 5 18 → False :=
  fun z0 z1 => w.entering 5 18 21 (by decide) (by decide) z0 z1

theorem c6179 (w : Witness) : Before w false 15 5 → Before w false 5 13 → False :=
  fun z0 z1 => w.entering 5 13 15 (by decide) (by decide) z0 z1

theorem c6181 (w : Witness) : Before w false 16 5 → Before w false 5 21 → False :=
  fun z0 z1 => w.entering 5 21 16 (by decide) (by decide) z0 z1

theorem c6182 (w : Witness) : Before w false 9 5 → Before w false 5 21 → False :=
  fun z0 z1 => w.entering 5 21 9 (by decide) (by decide) z0 z1

theorem c6183 (w : Witness) : Before w false 20 5 → Before w false 5 21 → False :=
  fun z0 z1 => w.entering 5 21 20 (by decide) (by decide) z0 z1

theorem c6184 (w : Witness) : Before w false 15 5 → Before w false 5 21 → False :=
  fun z0 z1 => w.entering 5 21 15 (by decide) (by decide) z0 z1

theorem c6187 (w : Witness) : Before w false 20 5 → Before w false 5 16 → False :=
  fun z0 z1 => w.entering 5 16 20 (by decide) (by decide) z0 z1

theorem c6193 (w : Witness) : Before w false 15 5 → Before w false 5 20 → False :=
  fun z0 z1 => w.entering 5 20 15 (by decide) (by decide) z0 z1

theorem c6194 (w : Witness) : Before w false 1 5 → Before w false 5 20 → False :=
  fun z0 z1 => w.entering 5 20 1 (by decide) (by decide) z0 z1

theorem c6196 (w : Witness) : Before w false 7 2 → Before w false 2 11 → False :=
  fun z0 z1 => w.entering 2 11 7 (by decide) (by decide) z0 z1

theorem c6197 (w : Witness) : Before w false 19 2 → Before w false 2 11 → False :=
  fun z0 z1 => w.entering 2 11 19 (by decide) (by decide) z0 z1

theorem c6198 (w : Witness) : Before w false 14 2 → Before w false 2 11 → False :=
  fun z0 z1 => w.entering 2 11 14 (by decide) (by decide) z0 z1

theorem c6201 (w : Witness) : Before w false 18 2 → Before w false 2 11 → False :=
  fun z0 z1 => w.entering 2 11 18 (by decide) (by decide) z0 z1

theorem c6209 (w : Witness) : Before w false 19 2 → Before w false 2 7 → False :=
  fun z0 z1 => w.entering 2 7 19 (by decide) (by decide) z0 z1

theorem c6210 (w : Witness) : Before w false 14 2 → Before w false 2 7 → False :=
  fun z0 z1 => w.entering 2 7 14 (by decide) (by decide) z0 z1

theorem c6212 (w : Witness) : Before w false 4 2 → Before w false 2 7 → False :=
  fun z0 z1 => w.entering 2 7 4 (by decide) (by decide) z0 z1

theorem c6214 (w : Witness) : Before w false 13 2 → Before w false 2 7 → False :=
  fun z0 z1 => w.entering 2 7 13 (by decide) (by decide) z0 z1

theorem c6216 (w : Witness) : Before w false 16 2 → Before w false 2 7 → False :=
  fun z0 z1 => w.entering 2 7 16 (by decide) (by decide) z0 z1

theorem c6221 (w : Witness) : Before w false 14 2 → Before w false 2 19 → False :=
  fun z0 z1 => w.entering 2 19 14 (by decide) (by decide) z0 z1

theorem c6222 (w : Witness) : Before w false 10 2 → Before w false 2 19 → False :=
  fun z0 z1 => w.entering 2 19 10 (by decide) (by decide) z0 z1

theorem c6223 (w : Witness) : Before w false 4 2 → Before w false 2 19 → False :=
  fun z0 z1 => w.entering 2 19 4 (by decide) (by decide) z0 z1

theorem c6224 (w : Witness) : Before w false 18 2 → Before w false 2 19 → False :=
  fun z0 z1 => w.entering 2 19 18 (by decide) (by decide) z0 z1

theorem c6225 (w : Witness) : Before w false 13 2 → Before w false 2 19 → False :=
  fun z0 z1 => w.entering 2 19 13 (by decide) (by decide) z0 z1

theorem c6228 (w : Witness) : Before w false 9 2 → Before w false 2 19 → False :=
  fun z0 z1 => w.entering 2 19 9 (by decide) (by decide) z0 z1

theorem c6232 (w : Witness) : Before w false 10 2 → Before w false 2 14 → False :=
  fun z0 z1 => w.entering 2 14 10 (by decide) (by decide) z0 z1

theorem c6233 (w : Witness) : Before w false 4 2 → Before w false 2 14 → False :=
  fun z0 z1 => w.entering 2 14 4 (by decide) (by decide) z0 z1

theorem c6234 (w : Witness) : Before w false 18 2 → Before w false 2 14 → False :=
  fun z0 z1 => w.entering 2 14 18 (by decide) (by decide) z0 z1

theorem c6235 (w : Witness) : Before w false 13 2 → Before w false 2 14 → False :=
  fun z0 z1 => w.entering 2 14 13 (by decide) (by decide) z0 z1

theorem c6236 (w : Witness) : Before w false 21 2 → Before w false 2 14 → False :=
  fun z0 z1 => w.entering 2 14 21 (by decide) (by decide) z0 z1

theorem c6237 (w : Witness) : Before w false 16 2 → Before w false 2 14 → False :=
  fun z0 z1 => w.entering 2 14 16 (by decide) (by decide) z0 z1

theorem c6239 (w : Witness) : Before w false 20 2 → Before w false 2 14 → False :=
  fun z0 z1 => w.entering 2 14 20 (by decide) (by decide) z0 z1

theorem c6242 (w : Witness) : Before w false 4 2 → Before w false 2 10 → False :=
  fun z0 z1 => w.entering 2 10 4 (by decide) (by decide) z0 z1

theorem c6246 (w : Witness) : Before w false 16 2 → Before w false 2 10 → False :=
  fun z0 z1 => w.entering 2 10 16 (by decide) (by decide) z0 z1

theorem c6251 (w : Witness) : Before w false 18 2 → Before w false 2 4 → False :=
  fun z0 z1 => w.entering 2 4 18 (by decide) (by decide) z0 z1

theorem c6252 (w : Witness) : Before w false 13 2 → Before w false 2 4 → False :=
  fun z0 z1 => w.entering 2 4 13 (by decide) (by decide) z0 z1

theorem c6253 (w : Witness) : Before w false 21 2 → Before w false 2 4 → False :=
  fun z0 z1 => w.entering 2 4 21 (by decide) (by decide) z0 z1

theorem c6254 (w : Witness) : Before w false 16 2 → Before w false 2 4 → False :=
  fun z0 z1 => w.entering 2 4 16 (by decide) (by decide) z0 z1

theorem c6259 (w : Witness) : Before w false 13 2 → Before w false 2 18 → False :=
  fun z0 z1 => w.entering 2 18 13 (by decide) (by decide) z0 z1

theorem c6266 (w : Witness) : Before w false 21 2 → Before w false 2 13 → False :=
  fun z0 z1 => w.entering 2 13 21 (by decide) (by decide) z0 z1

theorem c6273 (w : Witness) : Before w false 9 2 → Before w false 2 21 → False :=
  fun z0 z1 => w.entering 2 21 9 (by decide) (by decide) z0 z1

theorem c6275 (w : Witness) : Before w false 15 2 → Before w false 2 21 → False :=
  fun z0 z1 => w.entering 2 21 15 (by decide) (by decide) z0 z1

theorem c6276 (w : Witness) : Before w false 1 2 → Before w false 2 21 → False :=
  fun z0 z1 => w.entering 2 21 1 (by decide) (by decide) z0 z1

theorem c6277 (w : Witness) : Before w false 9 2 → Before w false 2 16 → False :=
  fun z0 z1 => w.entering 2 16 9 (by decide) (by decide) z0 z1

theorem c6278 (w : Witness) : Before w false 20 2 → Before w false 2 16 → False :=
  fun z0 z1 => w.entering 2 16 20 (by decide) (by decide) z0 z1

theorem c6285 (w : Witness) : Before w false 1 2 → Before w false 2 20 → False :=
  fun z0 z1 => w.entering 2 20 1 (by decide) (by decide) z0 z1

theorem c6287 (w : Witness) : Before w false 19 11 → Before w false 11 7 → False :=
  fun z0 z1 => w.entering 11 7 19 (by decide) (by decide) z0 z1

theorem c6288 (w : Witness) : Before w false 14 11 → Before w false 11 7 → False :=
  fun z0 z1 => w.entering 11 7 14 (by decide) (by decide) z0 z1

theorem c6299 (w : Witness) : Before w false 14 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 14 (by decide) (by decide) z0 z1

theorem c6300 (w : Witness) : Before w false 10 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 10 (by decide) (by decide) z0 z1

theorem c6301 (w : Witness) : Before w false 4 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 4 (by decide) (by decide) z0 z1

theorem c6302 (w : Witness) : Before w false 18 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 18 (by decide) (by decide) z0 z1

theorem c6304 (w : Witness) : Before w false 21 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 21 (by decide) (by decide) z0 z1

theorem c6306 (w : Witness) : Before w false 9 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 9 (by decide) (by decide) z0 z1

theorem c6307 (w : Witness) : Before w false 20 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 20 (by decide) (by decide) z0 z1

theorem c6308 (w : Witness) : Before w false 15 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 15 (by decide) (by decide) z0 z1

theorem c6309 (w : Witness) : Before w false 1 11 → Before w false 11 19 → False :=
  fun z0 z1 => w.entering 11 19 1 (by decide) (by decide) z0 z1

theorem c6310 (w : Witness) : Before w false 10 11 → Before w false 11 14 → False :=
  fun z0 z1 => w.entering 11 14 10 (by decide) (by decide) z0 z1

theorem c6320 (w : Witness) : Before w false 4 11 → Before w false 11 10 → False :=
  fun z0 z1 => w.entering 11 10 4 (by decide) (by decide) z0 z1

theorem c6321 (w : Witness) : Before w false 18 11 → Before w false 11 10 → False :=
  fun z0 z1 => w.entering 11 10 18 (by decide) (by decide) z0 z1

theorem c6324 (w : Witness) : Before w false 16 11 → Before w false 11 10 → False :=
  fun z0 z1 => w.entering 11 10 16 (by decide) (by decide) z0 z1

theorem c6328 (w : Witness) : Before w false 1 11 → Before w false 11 10 → False :=
  fun z0 z1 => w.entering 11 10 1 (by decide) (by decide) z0 z1

theorem c6329 (w : Witness) : Before w false 18 11 → Before w false 11 4 → False :=
  fun z0 z1 => w.entering 11 4 18 (by decide) (by decide) z0 z1

theorem c6330 (w : Witness) : Before w false 13 11 → Before w false 11 4 → False :=
  fun z0 z1 => w.entering 11 4 13 (by decide) (by decide) z0 z1

theorem c6332 (w : Witness) : Before w false 16 11 → Before w false 11 4 → False :=
  fun z0 z1 => w.entering 11 4 16 (by decide) (by decide) z0 z1

theorem c6337 (w : Witness) : Before w false 13 11 → Before w false 11 18 → False :=
  fun z0 z1 => w.entering 11 18 13 (by decide) (by decide) z0 z1

theorem c6338 (w : Witness) : Before w false 21 11 → Before w false 11 18 → False :=
  fun z0 z1 => w.entering 11 18 21 (by decide) (by decide) z0 z1

theorem c6344 (w : Witness) : Before w false 21 11 → Before w false 11 13 → False :=
  fun z0 z1 => w.entering 11 13 21 (by decide) (by decide) z0 z1

theorem c6345 (w : Witness) : Before w false 16 11 → Before w false 11 13 → False :=
  fun z0 z1 => w.entering 11 13 16 (by decide) (by decide) z0 z1

theorem c6350 (w : Witness) : Before w false 16 11 → Before w false 11 21 → False :=
  fun z0 z1 => w.entering 11 21 16 (by decide) (by decide) z0 z1

theorem c6351 (w : Witness) : Before w false 9 11 → Before w false 11 21 → False :=
  fun z0 z1 => w.entering 11 21 9 (by decide) (by decide) z0 z1

theorem c6352 (w : Witness) : Before w false 20 11 → Before w false 11 21 → False :=
  fun z0 z1 => w.entering 11 21 20 (by decide) (by decide) z0 z1

theorem c6354 (w : Witness) : Before w false 1 11 → Before w false 11 21 → False :=
  fun z0 z1 => w.entering 11 21 1 (by decide) (by decide) z0 z1

theorem c6356 (w : Witness) : Before w false 20 11 → Before w false 11 16 → False :=
  fun z0 z1 => w.entering 11 16 20 (by decide) (by decide) z0 z1

theorem c6358 (w : Witness) : Before w false 1 11 → Before w false 11 16 → False :=
  fun z0 z1 => w.entering 11 16 1 (by decide) (by decide) z0 z1

theorem c6359 (w : Witness) : Before w false 20 11 → Before w false 11 9 → False :=
  fun z0 z1 => w.entering 11 9 20 (by decide) (by decide) z0 z1

theorem c6360 (w : Witness) : Before w false 15 11 → Before w false 11 9 → False :=
  fun z0 z1 => w.entering 11 9 15 (by decide) (by decide) z0 z1

theorem c6361 (w : Witness) : Before w false 1 11 → Before w false 11 9 → False :=
  fun z0 z1 => w.entering 11 9 1 (by decide) (by decide) z0 z1

theorem c6363 (w : Witness) : Before w false 1 11 → Before w false 11 20 → False :=
  fun z0 z1 => w.entering 11 20 1 (by decide) (by decide) z0 z1

theorem c6364 (w : Witness) : Before w false 1 11 → Before w false 11 15 → False :=
  fun z0 z1 => w.entering 11 15 1 (by decide) (by decide) z0 z1

theorem c6365 (w : Witness) : Before w false 14 7 → Before w false 7 19 → False :=
  fun z0 z1 => w.entering 7 19 14 (by decide) (by decide) z0 z1

theorem c6366 (w : Witness) : Before w false 10 7 → Before w false 7 19 → False :=
  fun z0 z1 => w.entering 7 19 10 (by decide) (by decide) z0 z1

theorem c6367 (w : Witness) : Before w false 4 7 → Before w false 7 19 → False :=
  fun z0 z1 => w.entering 7 19 4 (by decide) (by decide) z0 z1

theorem c6368 (w : Witness) : Before w false 18 7 → Before w false 7 19 → False :=
  fun z0 z1 => w.entering 7 19 18 (by decide) (by decide) z0 z1

theorem c6369 (w : Witness) : Before w false 13 7 → Before w false 7 19 → False :=
  fun z0 z1 => w.entering 7 19 13 (by decide) (by decide) z0 z1

theorem c6370 (w : Witness) : Before w false 21 7 → Before w false 7 19 → False :=
  fun z0 z1 => w.entering 7 19 21 (by decide) (by decide) z0 z1

theorem c6373 (w : Witness) : Before w false 20 7 → Before w false 7 19 → False :=
  fun z0 z1 => w.entering 7 19 20 (by decide) (by decide) z0 z1

theorem c6376 (w : Witness) : Before w false 10 7 → Before w false 7 14 → False :=
  fun z0 z1 => w.entering 7 14 10 (by decide) (by decide) z0 z1

theorem c6386 (w : Witness) : Before w false 4 7 → Before w false 7 10 → False :=
  fun z0 z1 => w.entering 7 10 4 (by decide) (by decide) z0 z1

theorem c6387 (w : Witness) : Before w false 18 7 → Before w false 7 10 → False :=
  fun z0 z1 => w.entering 7 10 18 (by decide) (by decide) z0 z1

theorem c6389 (w : Witness) : Before w false 21 7 → Before w false 7 10 → False :=
  fun z0 z1 => w.entering 7 10 21 (by decide) (by decide) z0 z1

theorem c6395 (w : Witness) : Before w false 18 7 → Before w false 7 4 → False :=
  fun z0 z1 => w.entering 7 4 18 (by decide) (by decide) z0 z1

theorem c6396 (w : Witness) : Before w false 13 7 → Before w false 7 4 → False :=
  fun z0 z1 => w.entering 7 4 13 (by decide) (by decide) z0 z1

theorem c6398 (w : Witness) : Before w false 16 7 → Before w false 7 4 → False :=
  fun z0 z1 => w.entering 7 4 16 (by decide) (by decide) z0 z1

theorem c6399 (w : Witness) : Before w false 9 7 → Before w false 7 4 → False :=
  fun z0 z1 => w.entering 7 4 9 (by decide) (by decide) z0 z1

theorem c6403 (w : Witness) : Before w false 13 7 → Before w false 7 18 → False :=
  fun z0 z1 => w.entering 7 18 13 (by decide) (by decide) z0 z1

theorem c6404 (w : Witness) : Before w false 21 7 → Before w false 7 18 → False :=
  fun z0 z1 => w.entering 7 18 21 (by decide) (by decide) z0 z1

theorem c6405 (w : Witness) : Before w false 16 7 → Before w false 7 18 → False :=
  fun z0 z1 => w.entering 7 18 16 (by decide) (by decide) z0 z1

theorem c6410 (w : Witness) : Before w false 21 7 → Before w false 7 13 → False :=
  fun z0 z1 => w.entering 7 13 21 (by decide) (by decide) z0 z1

theorem c6416 (w : Witness) : Before w false 16 7 → Before w false 7 21 → False :=
  fun z0 z1 => w.entering 7 21 16 (by decide) (by decide) z0 z1

theorem c6417 (w : Witness) : Before w false 9 7 → Before w false 7 21 → False :=
  fun z0 z1 => w.entering 7 21 9 (by decide) (by decide) z0 z1

theorem c6418 (w : Witness) : Before w false 20 7 → Before w false 7 21 → False :=
  fun z0 z1 => w.entering 7 21 20 (by decide) (by decide) z0 z1

theorem c6419 (w : Witness) : Before w false 15 7 → Before w false 7 21 → False :=
  fun z0 z1 => w.entering 7 21 15 (by decide) (by decide) z0 z1

theorem c6420 (w : Witness) : Before w false 1 7 → Before w false 7 21 → False :=
  fun z0 z1 => w.entering 7 21 1 (by decide) (by decide) z0 z1

theorem c6425 (w : Witness) : Before w false 20 7 → Before w false 7 9 → False :=
  fun z0 z1 => w.entering 7 9 20 (by decide) (by decide) z0 z1

theorem c6428 (w : Witness) : Before w false 15 7 → Before w false 7 20 → False :=
  fun z0 z1 => w.entering 7 20 15 (by decide) (by decide) z0 z1

theorem c6429 (w : Witness) : Before w false 1 7 → Before w false 7 20 → False :=
  fun z0 z1 => w.entering 7 20 1 (by decide) (by decide) z0 z1

theorem c6431 (w : Witness) : Before w false 10 19 → Before w false 19 14 → False :=
  fun z0 z1 => w.entering 19 14 10 (by decide) (by decide) z0 z1

theorem c6432 (w : Witness) : Before w false 4 19 → Before w false 19 14 → False :=
  fun z0 z1 => w.entering 19 14 4 (by decide) (by decide) z0 z1

theorem c6433 (w : Witness) : Before w false 18 19 → Before w false 19 14 → False :=
  fun z0 z1 => w.entering 19 14 18 (by decide) (by decide) z0 z1

theorem c6434 (w : Witness) : Before w false 13 19 → Before w false 19 14 → False :=
  fun z0 z1 => w.entering 19 14 13 (by decide) (by decide) z0 z1

theorem c6441 (w : Witness) : Before w false 4 19 → Before w false 19 10 → False :=
  fun z0 z1 => w.entering 19 10 4 (by decide) (by decide) z0 z1

theorem c6443 (w : Witness) : Before w false 13 19 → Before w false 19 10 → False :=
  fun z0 z1 => w.entering 19 10 13 (by decide) (by decide) z0 z1

theorem c6444 (w : Witness) : Before w false 21 19 → Before w false 19 10 → False :=
  fun z0 z1 => w.entering 19 10 21 (by decide) (by decide) z0 z1

theorem c6447 (w : Witness) : Before w false 20 19 → Before w false 19 10 → False :=
  fun z0 z1 => w.entering 19 10 20 (by decide) (by decide) z0 z1

theorem c6450 (w : Witness) : Before w false 18 19 → Before w false 19 4 → False :=
  fun z0 z1 => w.entering 19 4 18 (by decide) (by decide) z0 z1

theorem c6451 (w : Witness) : Before w false 13 19 → Before w false 19 4 → False :=
  fun z0 z1 => w.entering 19 4 13 (by decide) (by decide) z0 z1

theorem c6452 (w : Witness) : Before w false 21 19 → Before w false 19 4 → False :=
  fun z0 z1 => w.entering 19 4 21 (by decide) (by decide) z0 z1

theorem c6458 (w : Witness) : Before w false 13 19 → Before w false 19 18 → False :=
  fun z0 z1 => w.entering 19 18 13 (by decide) (by decide) z0 z1

theorem c6459 (w : Witness) : Before w false 21 19 → Before w false 19 18 → False :=
  fun z0 z1 => w.entering 19 18 21 (by decide) (by decide) z0 z1

theorem c6465 (w : Witness) : Before w false 21 19 → Before w false 19 13 → False :=
  fun z0 z1 => w.entering 19 13 21 (by decide) (by decide) z0 z1

theorem c6471 (w : Witness) : Before w false 16 19 → Before w false 19 21 → False :=
  fun z0 z1 => w.entering 19 21 16 (by decide) (by decide) z0 z1

theorem c6472 (w : Witness) : Before w false 9 19 → Before w false 19 21 → False :=
  fun z0 z1 => w.entering 19 21 9 (by decide) (by decide) z0 z1

theorem c6474 (w : Witness) : Before w false 15 19 → Before w false 19 21 → False :=
  fun z0 z1 => w.entering 19 21 15 (by decide) (by decide) z0 z1

theorem c6475 (w : Witness) : Before w false 1 19 → Before w false 19 21 → False :=
  fun z0 z1 => w.entering 19 21 1 (by decide) (by decide) z0 z1

theorem c6476 (w : Witness) : Before w false 9 19 → Before w false 19 16 → False :=
  fun z0 z1 => w.entering 19 16 9 (by decide) (by decide) z0 z1

theorem c6477 (w : Witness) : Before w false 20 19 → Before w false 19 16 → False :=
  fun z0 z1 => w.entering 19 16 20 (by decide) (by decide) z0 z1

theorem c6480 (w : Witness) : Before w false 20 19 → Before w false 19 9 → False :=
  fun z0 z1 => w.entering 19 9 20 (by decide) (by decide) z0 z1

theorem c6483 (w : Witness) : Before w false 15 19 → Before w false 19 20 → False :=
  fun z0 z1 => w.entering 19 20 15 (by decide) (by decide) z0 z1

theorem c6484 (w : Witness) : Before w false 1 19 → Before w false 19 20 → False :=
  fun z0 z1 => w.entering 19 20 1 (by decide) (by decide) z0 z1

theorem c6485 (w : Witness) : Before w false 1 19 → Before w false 19 15 → False :=
  fun z0 z1 => w.entering 19 15 1 (by decide) (by decide) z0 z1

theorem c6486 (w : Witness) : Before w false 4 14 → Before w false 14 10 → False :=
  fun z0 z1 => w.entering 14 10 4 (by decide) (by decide) z0 z1

theorem c6487 (w : Witness) : Before w false 18 14 → Before w false 14 10 → False :=
  fun z0 z1 => w.entering 14 10 18 (by decide) (by decide) z0 z1

theorem c6491 (w : Witness) : Before w false 9 14 → Before w false 14 10 → False :=
  fun z0 z1 => w.entering 14 10 9 (by decide) (by decide) z0 z1

theorem c6494 (w : Witness) : Before w false 1 14 → Before w false 14 10 → False :=
  fun z0 z1 => w.entering 14 10 1 (by decide) (by decide) z0 z1

theorem c6495 (w : Witness) : Before w false 18 14 → Before w false 14 4 → False :=
  fun z0 z1 => w.entering 14 4 18 (by decide) (by decide) z0 z1

theorem c6501 (w : Witness) : Before w false 15 14 → Before w false 14 4 → False :=
  fun z0 z1 => w.entering 14 4 15 (by decide) (by decide) z0 z1

theorem c6503 (w : Witness) : Before w false 13 14 → Before w false 14 18 → False :=
  fun z0 z1 => w.entering 14 18 13 (by decide) (by decide) z0 z1

theorem c6504 (w : Witness) : Before w false 21 14 → Before w false 14 18 → False :=
  fun z0 z1 => w.entering 14 18 21 (by decide) (by decide) z0 z1

theorem c6505 (w : Witness) : Before w false 16 14 → Before w false 14 18 → False :=
  fun z0 z1 => w.entering 14 18 16 (by decide) (by decide) z0 z1

theorem c6507 (w : Witness) : Before w false 20 14 → Before w false 14 18 → False :=
  fun z0 z1 => w.entering 14 18 20 (by decide) (by decide) z0 z1

theorem c6508 (w : Witness) : Before w false 15 14 → Before w false 14 18 → False :=
  fun z0 z1 => w.entering 14 18 15 (by decide) (by decide) z0 z1

theorem c6510 (w : Witness) : Before w false 21 14 → Before w false 14 13 → False :=
  fun z0 z1 => w.entering 14 13 21 (by decide) (by decide) z0 z1

theorem c6517 (w : Witness) : Before w false 9 14 → Before w false 14 21 → False :=
  fun z0 z1 => w.entering 14 21 9 (by decide) (by decide) z0 z1

theorem c6518 (w : Witness) : Before w false 20 14 → Before w false 14 21 → False :=
  fun z0 z1 => w.entering 14 21 20 (by decide) (by decide) z0 z1

theorem c6520 (w : Witness) : Before w false 1 14 → Before w false 14 21 → False :=
  fun z0 z1 => w.entering 14 21 1 (by decide) (by decide) z0 z1

theorem c6522 (w : Witness) : Before w false 20 14 → Before w false 14 16 → False :=
  fun z0 z1 => w.entering 14 16 20 (by decide) (by decide) z0 z1

theorem c6525 (w : Witness) : Before w false 20 14 → Before w false 14 9 → False :=
  fun z0 z1 => w.entering 14 9 20 (by decide) (by decide) z0 z1

theorem c6527 (w : Witness) : Before w false 1 14 → Before w false 14 9 → False :=
  fun z0 z1 => w.entering 14 9 1 (by decide) (by decide) z0 z1

theorem c6528 (w : Witness) : Before w false 15 14 → Before w false 14 20 → False :=
  fun z0 z1 => w.entering 14 20 15 (by decide) (by decide) z0 z1

theorem c6529 (w : Witness) : Before w false 1 14 → Before w false 14 20 → False :=
  fun z0 z1 => w.entering 14 20 1 (by decide) (by decide) z0 z1

theorem c6530 (w : Witness) : Before w false 1 14 → Before w false 14 15 → False :=
  fun z0 z1 => w.entering 14 15 1 (by decide) (by decide) z0 z1

theorem c6531 (w : Witness) : Before w false 18 10 → Before w false 10 4 → False :=
  fun z0 z1 => w.entering 10 4 18 (by decide) (by decide) z0 z1

theorem c6534 (w : Witness) : Before w false 16 10 → Before w false 10 4 → False :=
  fun z0 z1 => w.entering 10 4 16 (by decide) (by decide) z0 z1

theorem c6539 (w : Witness) : Before w false 13 10 → Before w false 10 18 → False :=
  fun z0 z1 => w.entering 10 18 13 (by decide) (by decide) z0 z1

theorem c6546 (w : Witness) : Before w false 21 10 → Before w false 10 13 → False :=
  fun z0 z1 => w.entering 10 13 21 (by decide) (by decide) z0 z1

theorem c6552 (w : Witness) : Before w false 16 10 → Before w false 10 21 → False :=
  fun z0 z1 => w.entering 10 21 16 (by decide) (by decide) z0 z1

theorem c6553 (w : Witness) : Before w false 9 10 → Before w false 10 21 → False :=
  fun z0 z1 => w.entering 10 21 9 (by decide) (by decide) z0 z1

theorem c6554 (w : Witness) : Before w false 20 10 → Before w false 10 21 → False :=
  fun z0 z1 => w.entering 10 21 20 (by decide) (by decide) z0 z1

theorem c6555 (w : Witness) : Before w false 15 10 → Before w false 10 21 → False :=
  fun z0 z1 => w.entering 10 21 15 (by decide) (by decide) z0 z1

theorem c6556 (w : Witness) : Before w false 1 10 → Before w false 10 21 → False :=
  fun z0 z1 => w.entering 10 21 1 (by decide) (by decide) z0 z1

theorem c6558 (w : Witness) : Before w false 20 10 → Before w false 10 16 → False :=
  fun z0 z1 => w.entering 10 16 20 (by decide) (by decide) z0 z1

theorem c6560 (w : Witness) : Before w false 1 10 → Before w false 10 16 → False :=
  fun z0 z1 => w.entering 10 16 1 (by decide) (by decide) z0 z1

theorem c6563 (w : Witness) : Before w false 1 10 → Before w false 10 9 → False :=
  fun z0 z1 => w.entering 10 9 1 (by decide) (by decide) z0 z1

theorem c6564 (w : Witness) : Before w false 15 10 → Before w false 10 20 → False :=
  fun z0 z1 => w.entering 10 20 15 (by decide) (by decide) z0 z1

theorem c6565 (w : Witness) : Before w false 1 10 → Before w false 10 20 → False :=
  fun z0 z1 => w.entering 10 20 1 (by decide) (by decide) z0 z1

theorem c6566 (w : Witness) : Before w false 1 10 → Before w false 10 15 → False :=
  fun z0 z1 => w.entering 10 15 1 (by decide) (by decide) z0 z1

theorem c6567 (w : Witness) : Before w false 13 4 → Before w false 4 18 → False :=
  fun z0 z1 => w.entering 4 18 13 (by decide) (by decide) z0 z1

theorem c6568 (w : Witness) : Before w false 21 4 → Before w false 4 18 → False :=
  fun z0 z1 => w.entering 4 18 21 (by decide) (by decide) z0 z1

theorem c6571 (w : Witness) : Before w false 20 4 → Before w false 4 18 → False :=
  fun z0 z1 => w.entering 4 18 20 (by decide) (by decide) z0 z1

theorem c6574 (w : Witness) : Before w false 21 4 → Before w false 4 13 → False :=
  fun z0 z1 => w.entering 4 13 21 (by decide) (by decide) z0 z1

theorem c6580 (w : Witness) : Before w false 16 4 → Before w false 4 21 → False :=
  fun z0 z1 => w.entering 4 21 16 (by decide) (by decide) z0 z1

theorem c6581 (w : Witness) : Before w false 9 4 → Before w false 4 21 → False :=
  fun z0 z1 => w.entering 4 21 9 (by decide) (by decide) z0 z1

theorem c6582 (w : Witness) : Before w false 20 4 → Before w false 4 21 → False :=
  fun z0 z1 => w.entering 4 21 20 (by decide) (by decide) z0 z1

theorem c6584 (w : Witness) : Before w false 1 4 → Before w false 4 21 → False :=
  fun z0 z1 => w.entering 4 21 1 (by decide) (by decide) z0 z1

theorem c6585 (w : Witness) : Before w false 9 4 → Before w false 4 16 → False :=
  fun z0 z1 => w.entering 4 16 9 (by decide) (by decide) z0 z1

theorem c6589 (w : Witness) : Before w false 20 4 → Before w false 4 9 → False :=
  fun z0 z1 => w.entering 4 9 20 (by decide) (by decide) z0 z1

theorem c6592 (w : Witness) : Before w false 15 4 → Before w false 4 20 → False :=
  fun z0 z1 => w.entering 4 20 15 (by decide) (by decide) z0 z1

theorem c6593 (w : Witness) : Before w false 1 4 → Before w false 4 20 → False :=
  fun z0 z1 => w.entering 4 20 1 (by decide) (by decide) z0 z1

theorem c6595 (w : Witness) : Before w false 21 18 → Before w false 18 13 → False :=
  fun z0 z1 => w.entering 18 13 21 (by decide) (by decide) z0 z1

theorem c6598 (w : Witness) : Before w false 20 18 → Before w false 18 13 → False :=
  fun z0 z1 => w.entering 18 13 20 (by decide) (by decide) z0 z1

theorem c6599 (w : Witness) : Before w false 15 18 → Before w false 18 13 → False :=
  fun z0 z1 => w.entering 18 13 15 (by decide) (by decide) z0 z1

theorem c6600 (w : Witness) : Before w false 1 18 → Before w false 18 13 → False :=
  fun z0 z1 => w.entering 18 13 1 (by decide) (by decide) z0 z1

theorem c6601 (w : Witness) : Before w false 16 18 → Before w false 18 21 → False :=
  fun z0 z1 => w.entering 18 21 16 (by decide) (by decide) z0 z1

theorem c6602 (w : Witness) : Before w false 9 18 → Before w false 18 21 → False :=
  fun z0 z1 => w.entering 18 21 9 (by decide) (by decide) z0 z1

theorem c6603 (w : Witness) : Before w false 20 18 → Before w false 18 21 → False :=
  fun z0 z1 => w.entering 18 21 20 (by decide) (by decide) z0 z1

theorem c6604 (w : Witness) : Before w false 15 18 → Before w false 18 21 → False :=
  fun z0 z1 => w.entering 18 21 15 (by decide) (by decide) z0 z1

theorem c6605 (w : Witness) : Before w false 1 18 → Before w false 18 21 → False :=
  fun z0 z1 => w.entering 18 21 1 (by decide) (by decide) z0 z1

theorem c6606 (w : Witness) : Before w false 9 18 → Before w false 18 16 → False :=
  fun z0 z1 => w.entering 18 16 9 (by decide) (by decide) z0 z1

theorem c6607 (w : Witness) : Before w false 20 18 → Before w false 18 16 → False :=
  fun z0 z1 => w.entering 18 16 20 (by decide) (by decide) z0 z1

theorem c6609 (w : Witness) : Before w false 1 18 → Before w false 18 16 → False :=
  fun z0 z1 => w.entering 18 16 1 (by decide) (by decide) z0 z1

theorem c6610 (w : Witness) : Before w false 20 18 → Before w false 18 9 → False :=
  fun z0 z1 => w.entering 18 9 20 (by decide) (by decide) z0 z1

theorem c6613 (w : Witness) : Before w false 15 18 → Before w false 18 20 → False :=
  fun z0 z1 => w.entering 18 20 15 (by decide) (by decide) z0 z1

theorem c6614 (w : Witness) : Before w false 1 18 → Before w false 18 20 → False :=
  fun z0 z1 => w.entering 18 20 1 (by decide) (by decide) z0 z1

theorem c6615 (w : Witness) : Before w false 1 18 → Before w false 18 15 → False :=
  fun z0 z1 => w.entering 18 15 1 (by decide) (by decide) z0 z1

theorem c6616 (w : Witness) : Before w false 16 13 → Before w false 13 21 → False :=
  fun z0 z1 => w.entering 13 21 16 (by decide) (by decide) z0 z1

theorem c6617 (w : Witness) : Before w false 9 13 → Before w false 13 21 → False :=
  fun z0 z1 => w.entering 13 21 9 (by decide) (by decide) z0 z1

theorem c6618 (w : Witness) : Before w false 20 13 → Before w false 13 21 → False :=
  fun z0 z1 => w.entering 13 21 20 (by decide) (by decide) z0 z1

theorem c6619 (w : Witness) : Before w false 15 13 → Before w false 13 21 → False :=
  fun z0 z1 => w.entering 13 21 15 (by decide) (by decide) z0 z1

theorem c6621 (w : Witness) : Before w false 9 13 → Before w false 13 16 → False :=
  fun z0 z1 => w.entering 13 16 9 (by decide) (by decide) z0 z1

theorem c6624 (w : Witness) : Before w false 1 13 → Before w false 13 16 → False :=
  fun z0 z1 => w.entering 13 16 1 (by decide) (by decide) z0 z1

theorem c6625 (w : Witness) : Before w false 20 13 → Before w false 13 9 → False :=
  fun z0 z1 => w.entering 13 9 20 (by decide) (by decide) z0 z1

theorem c6628 (w : Witness) : Before w false 15 13 → Before w false 13 20 → False :=
  fun z0 z1 => w.entering 13 20 15 (by decide) (by decide) z0 z1

theorem c6629 (w : Witness) : Before w false 1 13 → Before w false 13 20 → False :=
  fun z0 z1 => w.entering 13 20 1 (by decide) (by decide) z0 z1

theorem c6630 (w : Witness) : Before w false 1 13 → Before w false 13 15 → False :=
  fun z0 z1 => w.entering 13 15 1 (by decide) (by decide) z0 z1

theorem c6631 (w : Witness) : Before w false 9 21 → Before w false 21 16 → False :=
  fun z0 z1 => w.entering 21 16 9 (by decide) (by decide) z0 z1

theorem c6632 (w : Witness) : Before w false 20 21 → Before w false 21 16 → False :=
  fun z0 z1 => w.entering 21 16 20 (by decide) (by decide) z0 z1

theorem c6635 (w : Witness) : Before w false 20 21 → Before w false 21 9 → False :=
  fun z0 z1 => w.entering 21 9 20 (by decide) (by decide) z0 z1

theorem c6638 (w : Witness) : Before w false 15 21 → Before w false 21 20 → False :=
  fun z0 z1 => w.entering 21 20 15 (by decide) (by decide) z0 z1

theorem c6639 (w : Witness) : Before w false 1 21 → Before w false 21 20 → False :=
  fun z0 z1 => w.entering 21 20 1 (by decide) (by decide) z0 z1

theorem c6640 (w : Witness) : Before w false 1 21 → Before w false 21 15 → False :=
  fun z0 z1 => w.entering 21 15 1 (by decide) (by decide) z0 z1

theorem c6641 (w : Witness) : Before w false 20 16 → Before w false 16 9 → False :=
  fun z0 z1 => w.entering 16 9 20 (by decide) (by decide) z0 z1

theorem c6642 (w : Witness) : Before w false 15 16 → Before w false 16 9 → False :=
  fun z0 z1 => w.entering 16 9 15 (by decide) (by decide) z0 z1

theorem c6643 (w : Witness) : Before w false 1 16 → Before w false 16 9 → False :=
  fun z0 z1 => w.entering 16 9 1 (by decide) (by decide) z0 z1

theorem c6644 (w : Witness) : Before w false 15 16 → Before w false 16 20 → False :=
  fun z0 z1 => w.entering 16 20 15 (by decide) (by decide) z0 z1

theorem c6645 (w : Witness) : Before w false 1 16 → Before w false 16 20 → False :=
  fun z0 z1 => w.entering 16 20 1 (by decide) (by decide) z0 z1

theorem c6646 (w : Witness) : Before w false 1 16 → Before w false 16 15 → False :=
  fun z0 z1 => w.entering 16 15 1 (by decide) (by decide) z0 z1

theorem c6647 (w : Witness) : Before w false 15 9 → Before w false 9 20 → False :=
  fun z0 z1 => w.entering 9 20 15 (by decide) (by decide) z0 z1

theorem c6649 (w : Witness) : Before w false 1 9 → Before w false 9 15 → False :=
  fun z0 z1 => w.entering 9 15 1 (by decide) (by decide) z0 z1

theorem c6650 (w : Witness) : Before w false 1 20 → Before w false 20 15 → False :=
  fun z0 z1 => w.entering 20 15 1 (by decide) (by decide) z0 z1

theorem c7017 (w : Witness) : Before w false 1 21 → Before w false 21 7 → Before w true 7 1 → Before w true 1 21 → False :=
  fun z0 z1 z2 z3 => w.middle 1 21 7 z0 z1 z2 z3

theorem c7020 (w : Witness) : Before w false 1 21 → Before w false 21 10 → Before w true 10 1 → Before w true 1 21 → False :=
  fun z0 z1 z2 z3 => w.middle 1 21 10 z0 z1 z2 z3

theorem c7051 (w : Witness) : Before w false 2 3 → Before w false 3 4 → Before w true 4 2 → Before w true 2 3 → False :=
  fun z0 z1 z2 z3 => w.middle 2 3 4 z0 z1 z2 z3

theorem c7053 (w : Witness) : Before w false 2 3 → Before w false 3 6 → Before w true 6 2 → Before w true 2 3 → False :=
  fun z0 z1 z2 z3 => w.middle 2 3 6 z0 z1 z2 z3

theorem c7056 (w : Witness) : Before w false 2 3 → Before w false 3 9 → Before w true 9 2 → Before w true 2 3 → False :=
  fun z0 z1 z2 z3 => w.middle 2 3 9 z0 z1 z2 z3

theorem c7066 (w : Witness) : Before w false 2 3 → Before w false 3 19 → Before w true 19 2 → Before w true 2 3 → False :=
  fun z0 z1 z2 z3 => w.middle 2 3 19 z0 z1 z2 z3

theorem c7068 (w : Witness) : Before w false 2 3 → Before w false 3 21 → Before w true 21 2 → Before w true 2 3 → False :=
  fun z0 z1 z2 z3 => w.middle 2 3 21 z0 z1 z2 z3

theorem c7076 (w : Witness) : Before w false 2 4 → Before w false 4 10 → Before w true 10 2 → Before w true 2 4 → False :=
  fun z0 z1 z2 z3 => w.middle 2 4 10 z0 z1 z2 z3

theorem c7077 (w : Witness) : Before w false 2 4 → Before w false 4 11 → Before w true 11 2 → Before w true 2 4 → False :=
  fun z0 z1 z2 z3 => w.middle 2 4 11 z0 z1 z2 z3

theorem c7078 (w : Witness) : Before w false 2 4 → Before w false 4 12 → Before w true 12 2 → Before w true 2 4 → False :=
  fun z0 z1 z2 z3 => w.middle 2 4 12 z0 z1 z2 z3

theorem c7079 (w : Witness) : Before w false 2 4 → Before w false 4 13 → Before w true 13 2 → Before w true 2 4 → False :=
  fun z0 z1 z2 z3 => w.middle 2 4 13 z0 z1 z2 z3

theorem c7089 (w : Witness) : Before w false 2 5 → Before w false 5 3 → Before w true 3 2 → Before w true 2 5 → False :=
  fun z0 z1 z2 z3 => w.middle 2 5 3 z0 z1 z2 z3

theorem c7109 (w : Witness) : Before w false 2 6 → Before w false 6 4 → Before w true 4 2 → Before w true 2 6 → False :=
  fun z0 z1 z2 z3 => w.middle 2 6 4 z0 z1 z2 z3

theorem c7127 (w : Witness) : Before w false 2 7 → Before w false 7 3 → Before w true 3 2 → Before w true 2 7 → False :=
  fun z0 z1 z2 z3 => w.middle 2 7 3 z0 z1 z2 z3

theorem c7128 (w : Witness) : Before w false 2 7 → Before w false 7 4 → Before w true 4 2 → Before w true 2 7 → False :=
  fun z0 z1 z2 z3 => w.middle 2 7 4 z0 z1 z2 z3

theorem c7141 (w : Witness) : Before w false 2 7 → Before w false 7 18 → Before w true 18 2 → Before w true 2 7 → False :=
  fun z0 z1 z2 z3 => w.middle 2 7 18 z0 z1 z2 z3

theorem c7146 (w : Witness) : Before w false 2 8 → Before w false 8 3 → Before w true 3 2 → Before w true 2 8 → False :=
  fun z0 z1 z2 z3 => w.middle 2 8 3 z0 z1 z2 z3

theorem c7147 (w : Witness) : Before w false 2 8 → Before w false 8 4 → Before w true 4 2 → Before w true 2 8 → False :=
  fun z0 z1 z2 z3 => w.middle 2 8 4 z0 z1 z2 z3

theorem c7151 (w : Witness) : Before w false 2 8 → Before w false 8 9 → Before w true 9 2 → Before w true 2 8 → False :=
  fun z0 z1 z2 z3 => w.middle 2 8 9 z0 z1 z2 z3

theorem c7152 (w : Witness) : Before w false 2 8 → Before w false 8 10 → Before w true 10 2 → Before w true 2 8 → False :=
  fun z0 z1 z2 z3 => w.middle 2 8 10 z0 z1 z2 z3

theorem c7154 (w : Witness) : Before w false 2 8 → Before w false 8 12 → Before w true 12 2 → Before w true 2 8 → False :=
  fun z0 z1 z2 z3 => w.middle 2 8 12 z0 z1 z2 z3

theorem c7155 (w : Witness) : Before w false 2 8 → Before w false 8 13 → Before w true 13 2 → Before w true 2 8 → False :=
  fun z0 z1 z2 z3 => w.middle 2 8 13 z0 z1 z2 z3

theorem c7184 (w : Witness) : Before w false 2 10 → Before w false 10 3 → Before w true 3 2 → Before w true 2 10 → False :=
  fun z0 z1 z2 z3 => w.middle 2 10 3 z0 z1 z2 z3

theorem c7208 (w : Witness) : Before w false 2 11 → Before w false 11 8 → Before w true 8 2 → Before w true 2 11 → False :=
  fun z0 z1 z2 z3 => w.middle 2 11 8 z0 z1 z2 z3

theorem c7222 (w : Witness) : Before w false 2 12 → Before w false 12 3 → Before w true 3 2 → Before w true 2 12 → False :=
  fun z0 z1 z2 z3 => w.middle 2 12 3 z0 z1 z2 z3

theorem c7223 (w : Witness) : Before w false 2 12 → Before w false 12 4 → Before w true 4 2 → Before w true 2 12 → False :=
  fun z0 z1 z2 z3 => w.middle 2 12 4 z0 z1 z2 z3

theorem c7236 (w : Witness) : Before w false 2 12 → Before w false 12 18 → Before w true 18 2 → Before w true 2 12 → False :=
  fun z0 z1 z2 z3 => w.middle 2 12 18 z0 z1 z2 z3

theorem c7239 (w : Witness) : Before w false 2 12 → Before w false 12 21 → Before w true 21 2 → Before w true 2 12 → False :=
  fun z0 z1 z2 z3 => w.middle 2 12 21 z0 z1 z2 z3

theorem c7245 (w : Witness) : Before w false 2 13 → Before w false 13 7 → Before w true 7 2 → Before w true 2 13 → False :=
  fun z0 z1 z2 z3 => w.middle 2 13 7 z0 z1 z2 z3

theorem c7255 (w : Witness) : Before w false 2 13 → Before w false 13 18 → Before w true 18 2 → Before w true 2 13 → False :=
  fun z0 z1 z2 z3 => w.middle 2 13 18 z0 z1 z2 z3

theorem c7260 (w : Witness) : Before w false 2 14 → Before w false 14 3 → Before w true 3 2 → Before w true 2 14 → False :=
  fun z0 z1 z2 z3 => w.middle 2 14 3 z0 z1 z2 z3

theorem c7261 (w : Witness) : Before w false 2 14 → Before w false 14 4 → Before w true 4 2 → Before w true 2 14 → False :=
  fun z0 z1 z2 z3 => w.middle 2 14 4 z0 z1 z2 z3

theorem c7263 (w : Witness) : Before w false 2 14 → Before w false 14 6 → Before w true 6 2 → Before w true 2 14 → False :=
  fun z0 z1 z2 z3 => w.middle 2 14 6 z0 z1 z2 z3

theorem c7274 (w : Witness) : Before w false 2 14 → Before w false 14 18 → Before w true 18 2 → Before w true 2 14 → False :=
  fun z0 z1 z2 z3 => w.middle 2 14 18 z0 z1 z2 z3

theorem c7277 (w : Witness) : Before w false 2 14 → Before w false 14 21 → Before w true 21 2 → Before w true 2 14 → False :=
  fun z0 z1 z2 z3 => w.middle 2 14 21 z0 z1 z2 z3

theorem c7297 (w : Witness) : Before w false 2 16 → Before w false 16 1 → Before w true 1 2 → Before w true 2 16 → False :=
  fun z0 z1 z2 z3 => w.middle 2 16 1 z0 z1 z2 z3

theorem c7317 (w : Witness) : Before w false 2 17 → Before w false 17 3 → Before w true 3 2 → Before w true 2 17 → False :=
  fun z0 z1 z2 z3 => w.middle 2 17 3 z0 z1 z2 z3

theorem c7318 (w : Witness) : Before w false 2 17 → Before w false 17 4 → Before w true 4 2 → Before w true 2 17 → False :=
  fun z0 z1 z2 z3 => w.middle 2 17 4 z0 z1 z2 z3

theorem c7326 (w : Witness) : Before w false 2 17 → Before w false 17 12 → Before w true 12 2 → Before w true 2 17 → False :=
  fun z0 z1 z2 z3 => w.middle 2 17 12 z0 z1 z2 z3

theorem c7334 (w : Witness) : Before w false 2 17 → Before w false 17 21 → Before w true 21 2 → Before w true 2 17 → False :=
  fun z0 z1 z2 z3 => w.middle 2 17 21 z0 z1 z2 z3

theorem c7337 (w : Witness) : Before w false 2 18 → Before w false 18 4 → Before w true 4 2 → Before w true 2 18 → False :=
  fun z0 z1 z2 z3 => w.middle 2 18 4 z0 z1 z2 z3

theorem c7343 (w : Witness) : Before w false 2 18 → Before w false 18 10 → Before w true 10 2 → Before w true 2 18 → False :=
  fun z0 z1 z2 z3 => w.middle 2 18 10 z0 z1 z2 z3

theorem c7353 (w : Witness) : Before w false 2 18 → Before w false 18 21 → Before w true 21 2 → Before w true 2 18 → False :=
  fun z0 z1 z2 z3 => w.middle 2 18 21 z0 z1 z2 z3


end ThreeStacks.OrderProof
