import Ramsey556.Split17.Check
import Ramsey556.Split17.Data

namespace Ramsey556.Split17

set_option maxRecDepth 65536
set_option maxHeartbeats 0
set_option Elab.async false

private noncomputable def trace0 : Trace :=
 (.branch 6
 (.branch 1
 (.cycle false 0x6394831002d)
 (.branch 8
 (.cycle false 0x862d49080cd)
 (.branch 9
 (.cycle false 0x962d48080cd)
 (.branch 10
 (.cycle false 0xa62d28080cd)
 (.branch 11
 (.cycle false 0xb62928080cd)
 (.branch 12
 (.cycle false 0xc5a928080cd)
 (.branch 2
 (.branch 3
 (.branch 4
 (.branch 5
 (.branch 7
 (.branch 19
 (.branch 14
 (.cycle false 0x6394831002e)
 (.branch 21
 (.cycle false 0x862d49080ce)
 (.branch 22
 (.cycle false 0x962d48080ce)
 (.branch 23
 (.cycle false 0xa62d28080ce)
 (.branch 24
 (.cycle false 0xb62928080ce)
 (.branch 25
 (.cycle false 0xc5a928080ce)
 (.branch 15
 (.branch 16
 (.branch 17
 (.branch 18
 (.cycle false 0x7699c520c40)
 (.cycle true 0x5511234082e))
 (.cycle true 0x4515234082e))
 (.cycle true 0x3515244082e))
 (.cycle true 0x25152440c2e))))))))
 (.branch 14
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.branch 16
 (.cycle false 0x3398a41002e)
 (.branch 17
 (.cycle false 0x4398a31002e)
 (.branch 18
 (.cycle false 0x5398831002e)
 (.branch 20
 (.cycle false 0x7314831002e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 32
 (.branch 27
 (.cycle false 0x6394831002f)
 (.branch 34
 (.cycle false 0x862d49080cf)
 (.branch 35
 (.cycle false 0x962d48080cf)
 (.branch 36
 (.cycle false 0xa62d28080cf)
 (.branch 37
 (.cycle false 0xb62928080cf)
 (.branch 38
 (.cycle false 0xc5a928080cf)
 (.branch 28
 (.branch 29
 (.branch 30
 (.branch 31
 (.cycle false 0x7699e520c40)
 (.cycle true 0x5511234082f))
 (.cycle true 0x4515234082f))
 (.cycle true 0x3515244082f))
 (.cycle true 0x25152440c2f))))))))
 (.branch 27
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.branch 29
 (.cycle false 0x3398a41002f)
 (.branch 30
 (.cycle false 0x4398a31002f)
 (.branch 31
 (.cycle false 0x5398831002f)
 (.branch 33
 (.cycle false 0x7314831002f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.cycle false 0xc72dea4a020)
 (.cycle true 0xb2a4881844f))
 (.cycle true 0xa2a4881844f))
 (.cycle true 0x92a8881844f))
 (.cycle true 0x82a8891844f)))))))
 (.cycle true 0x6511234082f)))
 (.cycle true 0xc2a4881844e))
 (.cycle true 0xb2a4881844e))
 (.cycle true 0xa2a4881844e))
 (.cycle true 0x92a8881844e))
 (.cycle true 0x82a8891844e)))))))
 (.cycle true 0x6511234082e)))
 (.cycle true 0x7511234082d))
 (.cycle true 0x5511234082d))
 (.cycle true 0x4515234082d))
 (.cycle true 0x3515244082d))
 (.cycle true 0x25152440c2d))))))))
 (.branch 1
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.branch 3
 (.cycle false 0x3398a41002d)
 (.branch 4
 (.cycle false 0x4398a31002d)
 (.branch 5
 (.cycle false 0x5398831002d)
 (.branch 7
 (.cycle false 0x7314831002d)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 24
 (.branch 15
 (.cycle false 0xb629280804e)
 (.branch 16
 (.cycle false 0xb629280806e)
 (.branch 17
 (.cycle false 0xb629280808e)
 (.branch 18
 (.cycle false 0xb62928080ae)
 (.branch 19
 (.cycle false 0xb62928080ce)
 (.branch 20
 (.cycle false 0xb62928080ee)
 (.branch 14
 (.branch 21
 (.branch 22
 (.branch 23
 (.cycle false 0xc6adca4a020)
 (.cycle true 0xa2a4881844e))
 (.cycle true 0x92a8881844e))
 (.cycle true 0x82a8891844e))
 (.cycle true 0x25152440c2e))))))))
 (.branch 15
 (.branch 14
 (.cycle false 0x2398a41802e)
 (.branch 21
 (.cycle false 0x862d490804e)
 (.branch 22
 (.cycle false 0x962d480804e)
 (.branch 23
 (.cycle false 0xa62d280804e)
 (.branch 25
 (.cycle false 0xc5a9280804e)
 (.branch 16
 (.branch 17
 (.branch 18
 (.branch 19
 (.branch 20
 (.branch 32
 (.branch 27
 (.cycle false 0x6394831002f)
 (.branch 34
 (.cycle false 0x862d49080cf)
 (.branch 35
 (.cycle false 0x962d48080cf)
 (.branch 36
 (.cycle false 0xa62d28080cf)
 (.branch 37
 (.cycle false 0xb62928080cf)
 (.branch 38
 (.cycle false 0xc5a928080cf)
 (.branch 28
 (.branch 29
 (.branch 30
 (.branch 31
 (.cycle false 0x7719e520c40)
 (.cycle true 0x5511234082f))
 (.cycle true 0x4515234082f))
 (.cycle true 0x3515244082f))
 (.cycle true 0x25152440c2f))))))))
 (.branch 27
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.branch 29
 (.cycle false 0x3398a41002f)
 (.branch 30
 (.cycle false 0x4398a31002f)
 (.branch 31
 (.cycle false 0x5398831002f)
 (.branch 33
 (.cycle false 0x7314831002f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.cycle false 0xc6adea4a020)
 (.cycle true 0xb2a4881844f))
 (.cycle true 0xa2a4881844f))
 (.cycle true 0x92a8881844f))
 (.cycle true 0x82a8891844f)))))))
 (.cycle true 0x6511234082f)))
 (.cycle true 0x7511234082e))
 (.cycle true 0x6511234082e))
 (.cycle true 0x5511234082e))
 (.cycle true 0x4515234082e))
 (.cycle true 0x3515244082e)))))))
 (.cycle true 0xb2a4881844e)))
 (.cycle true 0xc2a4881844d))
 (.cycle true 0xb2a4881844d))
 (.cycle true 0xa2a4881844d))
 (.cycle true 0x92a8881844d))
 (.cycle true 0x82a8891844d)))))))
 (.cycle true 0x6511234082d)))

private theorem valid0 : check (core13 0) (fun _ => 0) trace0 = true := by decide +kernel

private noncomputable def trace1 : Trace :=
 (.branch 7
 (.branch 20
 (.branch 33
 (.branch 46
 (.branch 4
 (.branch 18
 (.cycle false 0x571da418820)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 13
 (.cycle false 0xe41da418820)
 (.branch 31
 (.cycle false 0x579da418820)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 26
 (.cycle false 0xf41da418820)
 (.branch 44
 (.cycle false 0x581da418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397052507)
 (.cycle true 0xb1242801cb0))
 (.cycle true 0xa1242801cb0))
 (.cycle true 0x91282801cb0))
 (.cycle true 0x81282901cb0))))
 (.cycle true 0xc1242801caf))
 (.cycle true 0xb1242801caf))
 (.cycle true 0xa1242801caf))
 (.cycle true 0x91282801caf))
 (.cycle true 0x81282901caf))))
 (.cycle true 0xc1242801cae))
 (.cycle true 0xb1242801cae))
 (.cycle true 0xa1242801cae))
 (.cycle true 0x91282801cae))
 (.cycle true 0x81282901cae)))
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 17
 (.branch 0
 (.cycle false 0xd41dc418820)
 (.branch 5
 (.cycle false 0x569dc418820)
 (.branch 31
 (.cycle false 0x579dc418820)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 26
 (.cycle false 0xf41dc418820)
 (.branch 44
 (.cycle false 0x581dc418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xf6357052507)
 (.cycle true 0xb1242801cb0))
 (.cycle true 0xa1242801cb0))
 (.cycle true 0x91282801cb0))
 (.cycle true 0x81282901cb0))))
 (.cycle true 0xc1242801caf))
 (.cycle true 0xb1242801caf))
 (.cycle true 0xa1242801caf))
 (.cycle true 0x91282801caf))
 (.cycle true 0x81282901caf)))))
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 51
 (.cycle false 0x106396d52507)
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.branch 44
 (.branch 45
 (.branch 0
 (.cycle false 0xd3c0c418820)
 (.branch 13
 (.cycle false 0xe3c0c418820)
 (.branch 26
 (.cycle false 0xf3c0c418820)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.cycle false 0xe6356f52507)
 (.cycle true 0xb1a44809c0f))
 (.cycle true 0xa1a44809c0f))
 (.cycle true 0x91a84809c0f))
 (.cycle true 0x81a84909c0f)))))
 (.cycle true 0xc1242801cd0))
 (.cycle true 0xc1242801cb0))
 (.cycle true 0xc1242801c90))
 (.cycle true 0xc1242801c70))
 (.cycle true 0xc1a42801c50))
 (.cycle true 0xc1a44801c30))
 (.cycle true 0xc1a44809c10)))
 (.cycle true 0xc1242801c8e))
 (.cycle true 0xb1242801c8e))
 (.cycle true 0xa1242801c8e))
 (.cycle true 0x91282801c8e))
 (.cycle true 0x81282901c8e)))
 (.cycle true 0xc1242801c8d))
 (.cycle true 0xb1242801c8d))
 (.cycle true 0xa1242801c8d))
 (.cycle true 0x91282801c8d))
 (.cycle true 0x81282901c8d)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.branch 44
 (.branch 45
 (.branch 4
 (.branch 47
 (.cycle false 0x1041da418820)
 (.branch 18
 (.cycle false 0x571da418820)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 13
 (.cycle false 0xe41da418820)
 (.branch 31
 (.cycle false 0x579da418820)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 26
 (.cycle false 0xf41da418820)
 (.branch 3
 (.cycle false 0x103148d18820)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.cycle false 0xf6396d52507)
 (.cycle true 0xb1242801c6d))
 (.cycle true 0xa1242801c6d))
 (.cycle true 0x91282801c6d))
 (.cycle true 0x81282901c6d))))
 (.cycle true 0xc1242801caf))
 (.cycle true 0xb1242801caf))
 (.cycle true 0xa1242801caf))
 (.cycle true 0x91282801caf))
 (.cycle true 0x81282901caf))))
 (.cycle true 0xc1242801cae))
 (.cycle true 0xb1242801cae))
 (.cycle true 0xa1242801cae))
 (.cycle true 0x91282801cae))
 (.cycle true 0x81282901cae))))
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 17
 (.branch 0
 (.cycle false 0xd41dc418820)
 (.branch 47
 (.cycle false 0x1041dc418820)
 (.branch 5
 (.cycle false 0x569dc418820)
 (.branch 31
 (.cycle false 0x579dc418820)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 26
 (.cycle false 0xf41dc418820)
 (.branch 16
 (.cycle false 0x103148e18820)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.cycle false 0xf6356e52507)
 (.cycle true 0xb1242801c6e))
 (.cycle true 0xa1242801c6e))
 (.cycle true 0x91282801c6e))
 (.cycle true 0x81282901c6e))))
 (.cycle true 0xc1242801caf))
 (.cycle true 0xb1242801caf))
 (.cycle true 0xa1242801caf))
 (.cycle true 0x91282801caf))
 (.cycle true 0x81282901caf))))))
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 38
 (.cycle false 0xf6396d52507)
 (.branch 26
 (.branch 27
 (.branch 28
 (.branch 29
 (.branch 30
 (.cycle false 0x103148f18820)
 (.cycle true 0xc1242801c8f))
 (.cycle true 0xc1242801c6f))
 (.cycle true 0xc1a42801c4f))
 (.cycle true 0xc1a44801c2f))
 (.cycle true 0xc1a44809c0f)))
 (.cycle true 0xc1242801c8e))
 (.cycle true 0xb1242801c8e))
 (.cycle true 0xa1242801c8e))
 (.cycle true 0x91282801c8e))
 (.cycle true 0x81282901c8e)))
 (.cycle true 0xc1242801c8d))
 (.cycle true 0xb1242801c8d))
 (.cycle true 0xa1242801c8d))
 (.cycle true 0x91282801c8d))
 (.cycle true 0x81282901c8d)))
 (.cycle true 0x712829020d0))
 (.cycle true 0x712829020b0))
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))
 (.branch 26
 (.branch 27
 (.branch 28
 (.branch 29
 (.branch 30
 (.branch 31
 (.branch 32
 (.branch 4
 (.branch 34
 (.cycle false 0xf41da418820)
 (.branch 18
 (.cycle false 0x571da418820)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 13
 (.cycle false 0xe41da418820)
 (.branch 3
 (.cycle false 0xf3148d18820)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 2
 (.cycle false 0xf3146468820)
 (.branch 1
 (.cycle false 0xf3146223420)
 (.branch 38
 (.cycle false 0xf62d4941da4)
 (.branch 17
 (.cycle false 0xe62d4941da4)
 (.branch 46
 (.branch 44
 (.cycle false 0x581da418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xe6357052507)
 (.cycle true 0xb1242801cb0))
 (.cycle true 0xa1242801cb0))
 (.cycle true 0x91282801cb0))
 (.cycle true 0x81282901cb0)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xf3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))))))
 (.cycle true 0xc1242801c6d))
 (.cycle true 0xb1242801c6d))
 (.cycle true 0xa1242801c6d))
 (.cycle true 0x91282801c6d))
 (.cycle true 0x81282901c6d))))
 (.cycle true 0xc1242801cae))
 (.cycle true 0xb1242801cae))
 (.cycle true 0xa1242801cae))
 (.cycle true 0x91282801cae))
 (.cycle true 0x81282901cae))))
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 17
 (.branch 0
 (.cycle false 0xd41dc418820)
 (.branch 34
 (.cycle false 0xf41dc418820)
 (.branch 5
 (.cycle false 0x569dc418820)
 (.branch 16
 (.cycle false 0xf3148e18820)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 15
 (.cycle false 0xf3146470820)
 (.branch 14
 (.cycle false 0xf3146223820)
 (.branch 38
 (.cycle false 0xf62d4941dc4)
 (.branch 46
 (.branch 44
 (.cycle false 0x581dc418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xe6357052507)
 (.cycle true 0xb1242801cb0))
 (.cycle true 0xa1242801cb0))
 (.cycle true 0x91282801cb0))
 (.cycle true 0x81282901cb0)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xf3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010))))))
 (.cycle true 0xc1242801c6e))
 (.cycle true 0xb1242801c6e))
 (.cycle true 0xa1242801c6e))
 (.cycle true 0x91282801c6e))
 (.cycle true 0x81282901c6e))))))
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 46
 (.branch 51
 (.cycle false 0x106396d52507)
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xf3149018820)
 (.cycle true 0xc1242801c90))
 (.cycle true 0xc1242801c70))
 (.cycle true 0xc1a42801c50))
 (.cycle true 0xc1a44801c30))
 (.cycle true 0xc1a44809c10)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xf3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))
 (.cycle true 0xc1242801c8e))
 (.cycle true 0xb1242801c8e))
 (.cycle true 0xa1242801c8e))
 (.cycle true 0x91282801c8e))
 (.cycle true 0x81282901c8e)))
 (.cycle true 0xc1242801c8d))
 (.cycle true 0xb1242801c8d))
 (.cycle true 0xa1242801c8d))
 (.cycle true 0x91282801c8d))
 (.cycle true 0x81282901c8d)))
 (.cycle true 0x712829020cf))
 (.cycle true 0x712829020af))
 (.cycle true 0x7128290208f))
 (.cycle true 0x7128290206f))
 (.cycle true 0x71a8290204f))
 (.cycle true 0x71a8490202f))
 (.cycle true 0x71a8490a00f)))
 (.branch 13
 (.branch 14
 (.branch 15
 (.branch 16
 (.branch 17
 (.branch 18
 (.branch 19
 (.branch 4
 (.branch 21
 (.cycle false 0xe41da418820)
 (.branch 3
 (.cycle false 0xe3148d18820)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 2
 (.cycle false 0xe3146468820)
 (.branch 1
 (.cycle false 0xe3146223420)
 (.branch 25
 (.cycle false 0xe62d4941da4)
 (.branch 30
 (.branch 29
 (.cycle false 0xe3148f18820)
 (.branch 33
 (.cycle false 0xd62d4941de4)
 (.cycle true 0x7128290206f)))
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 26
 (.cycle false 0xf41da418820)
 (.branch 31
 (.cycle false 0x579da418820)
 (.branch 46
 (.branch 44
 (.cycle false 0x581da418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xf6357052507)
 (.cycle true 0xb1242801cb0))
 (.cycle true 0xa1242801cb0))
 (.cycle true 0x91282801cb0))
 (.cycle true 0x81282901cb0)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xe3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))))
 (.cycle true 0xc1242801c8f))
 (.cycle true 0xb1242801c8f))
 (.cycle true 0xa1242801c8f))
 (.cycle true 0x91282801c8f))
 (.cycle true 0x81282901c8f))
 (.cycle true 0x7128290208f))))))
 (.cycle true 0xc1242801c6d))
 (.cycle true 0xb1242801c6d))
 (.cycle true 0xa1242801c6d))
 (.cycle true 0x91282801c6d))
 (.cycle true 0x81282901c6d))))
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 30
 (.branch 29
 (.cycle false 0xe3148f18820)
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 0
 (.cycle false 0xd41de418820)
 (.branch 21
 (.cycle false 0xe41de418820)
 (.branch 5
 (.cycle false 0x569de418820)
 (.branch 28
 (.cycle false 0xe3146478820)
 (.branch 27
 (.cycle false 0xe3146223c20)
 (.branch 25
 (.cycle false 0xe62d4941de4)
 (.branch 46
 (.branch 44
 (.cycle false 0x581de418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xf6357052507)
 (.cycle true 0xb1242801cb0))
 (.cycle true 0xa1242801cb0))
 (.cycle true 0x91282801cb0))
 (.cycle true 0x81282901cb0)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xe3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))))))))
 (.cycle true 0xc1242801c6f))
 (.cycle true 0xb1242801c6f))
 (.cycle true 0xa1242801c6f))
 (.cycle true 0x91282801c6f))
 (.cycle true 0x81282901c6f))
 (.cycle true 0x7128290206f)))
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 46
 (.branch 51
 (.cycle false 0x1063d6d52507)
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xe3149018820)
 (.cycle true 0xc1242801c90))
 (.cycle true 0xc1242801c70))
 (.cycle true 0xc1a42801c50))
 (.cycle true 0xc1a44801c30))
 (.cycle true 0xc1a44809c10)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xe3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))
 (.cycle true 0xc1242801c8f))
 (.cycle true 0xb1242801c8f))
 (.cycle true 0xa1242801c8f))
 (.cycle true 0x91282801c8f))
 (.cycle true 0x81282901c8f))
 (.cycle true 0x7128290208f)))
 (.cycle true 0xc1242801c8d))
 (.cycle true 0xb1242801c8d))
 (.cycle true 0xa1242801c8d))
 (.cycle true 0x91282801c8d))
 (.cycle true 0x81282901c8d)))
 (.cycle true 0x712829020ce))
 (.cycle true 0x712829020ae))
 (.cycle true 0x7128290208e))
 (.cycle true 0x7128290206e))
 (.cycle true 0x71a8290204e))
 (.cycle true 0x71a8490202e))
 (.cycle true 0x71a8490a00e)))
 (.branch 0
 (.branch 1
 (.branch 2
 (.branch 3
 (.branch 4
 (.branch 5
 (.branch 6
 (.branch 19
 (.branch 13
 (.cycle false 0xe334a418820)
 (.branch 20
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 18
 (.cycle false 0xd338a418820)
 (.branch 26
 (.branch 32
 (.cycle false 0xf334a418820)
 (.branch 33
 (.cycle false 0xf3b8c418820)
 (.cycle true 0x712829020cf)))
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 46
 (.branch 39
 (.cycle false 0x103b8c418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397052507)
 (.cycle true 0xb1a44809c10))
 (.cycle true 0xa1a44809c10))
 (.cycle true 0x91a84809c10))
 (.cycle true 0x81a84909c10)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xd3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))
 (.cycle true 0xc1a44809c0f))
 (.cycle true 0xb1a44809c0f))
 (.cycle true 0xa1a44809c0f))
 (.cycle true 0x91a84809c0f))
 (.cycle true 0x81a84909c0f))
 (.cycle true 0x71a8490a00f))))
 (.cycle true 0xc1a44809c0e))
 (.cycle true 0xb1a44809c0e))
 (.cycle true 0xa1a44809c0e))
 (.cycle true 0x91a84809c0e))
 (.cycle true 0x81a84909c0e))
 (.cycle true 0x71a8490a00e)))
 (.branch 20
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 30
 (.branch 29
 (.cycle false 0xd3148f18820)
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 8
 (.cycle false 0xd41de418820)
 (.branch 13
 (.cycle false 0xe41de418820)
 (.branch 18
 (.cycle false 0x571de418820)
 (.branch 28
 (.cycle false 0xd3146478820)
 (.branch 27
 (.cycle false 0xd3146223c20)
 (.branch 17
 (.cycle false 0xf62d4941dc4)
 (.branch 12
 (.cycle false 0xd62d4941de4)
 (.branch 46
 (.branch 44
 (.cycle false 0x581de418820)
 (.branch 47
 (.branch 48
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397052507)
 (.cycle true 0xb1242801cb0))
 (.cycle true 0xa1242801cb0))
 (.cycle true 0x91282801cb0))
 (.cycle true 0x81282901cb0)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xd3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010))))))))))
 (.cycle true 0xc1242801c6f))
 (.cycle true 0xb1242801c6f))
 (.cycle true 0xa1242801c6f))
 (.cycle true 0x91282801c6f))
 (.cycle true 0x81282901c6f))
 (.cycle true 0x7128290206f)))
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 46
 (.branch 51
 (.cycle false 0x1063d6e52507)
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xd3149018820)
 (.cycle true 0xc1242801c90))
 (.cycle true 0xc1242801c70))
 (.cycle true 0xc1a42801c50))
 (.cycle true 0xc1a44801c30))
 (.cycle true 0xc1a44809c10)))
 (.branch 39
 (.branch 40
 (.branch 41
 (.branch 42
 (.branch 43
 (.cycle false 0xd3149018820)
 (.cycle true 0x71282902090))
 (.cycle true 0x71282902070))
 (.cycle true 0x71a82902050))
 (.cycle true 0x71a84902030))
 (.cycle true 0x71a8490a010)))
 (.cycle true 0xc1242801c8f))
 (.cycle true 0xb1242801c8f))
 (.cycle true 0xa1242801c8f))
 (.cycle true 0x91282801c8f))
 (.cycle true 0x81282901c8f))
 (.cycle true 0x7128290208f)))
 (.cycle true 0xc1242801cce))
 (.cycle true 0xb1242801cce))
 (.cycle true 0xa1242801cce))
 (.cycle true 0x91282801cce))
 (.cycle true 0x81282901cce))
 (.cycle true 0x712829020ce)))
 (.cycle true 0x712829020cd))
 (.cycle true 0x712829020ad))
 (.cycle true 0x7128290208d))
 (.cycle true 0x7128290206d))
 (.cycle true 0x71a8290204d))
 (.cycle true 0x71a8490202d))
 (.cycle true 0x71a8490a00d)))

private theorem valid1 : check (core13 1) (fun _ => 0) trace1 = true := by decide +kernel

private noncomputable def trace2 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.branch 3
 (.cycle false 0x3398a41002d)
 (.branch 4
 (.cycle false 0x4398a31002d)
 (.branch 5
 (.cycle false 0x5398831002d)
 (.branch 6
 (.cycle false 0x6394831002d)
 (.branch 7
 (.cycle false 0x7314831002d)
 (.branch 8
 (.cycle false 0x862d490082d)
 (.cycle true 0x822c6a0a44d)))))))))
 (.branch 8
 (.branch 2
 (.cycle false 0x862d490044d)
 (.branch 3
 (.cycle false 0x862d490046d)
 (.branch 4
 (.cycle false 0x862d490048d)
 (.branch 5
 (.cycle false 0x862d49004ad)
 (.branch 6
 (.cycle false 0x862d49004cd)
 (.branch 7
 (.cycle false 0x862d49004ed)
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 14
 (.branch 13
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.branch 16
 (.cycle false 0x3398a41002e)
 (.branch 17
 (.cycle false 0x4398a31002e)
 (.branch 18
 (.cycle false 0x5398831002e)
 (.branch 19
 (.cycle false 0x6394831002e)
 (.branch 20
 (.cycle false 0x7314831002e)
 (.branch 21
 (.cycle false 0x862d490082e)
 (.cycle true 0x822c6a0a44e)))))))))
 (.branch 21
 (.branch 15
 (.cycle false 0x862d490044e)
 (.branch 16
 (.cycle false 0x862d490046e)
 (.branch 17
 (.cycle false 0x862d490048e)
 (.branch 18
 (.cycle false 0x862d49004ae)
 (.branch 19
 (.cycle false 0x862d49004ce)
 (.branch 20
 (.cycle false 0x862d49004ee)
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 36
 (.branch 27
 (.cycle false 0xa62d280082f)
 (.branch 28
 (.cycle false 0xa62d280044f)
 (.branch 29
 (.cycle false 0xa62d280046f)
 (.branch 30
 (.cycle false 0xa62d280048f)
 (.branch 31
 (.cycle false 0xa62d28004af)
 (.branch 32
 (.cycle false 0xa62d28004cf)
 (.branch 33
 (.cycle false 0xa62d28004ef)
 (.branch 34
 (.branch 35
 (.cycle false 0xc72daa7a500)
 (.cycle true 0x922c6a1202f))
 (.cycle true 0x822c6a1242f)))))))))
 (.branch 27
 (.branch 26
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.cycle true 0xa22c690a04f)))
 (.cycle true 0xa22c691202f)))
 (.cycle true 0xc228691202e))
 (.cycle true 0xb228691202e))
 (.cycle true 0xa22c691202e))
 (.cycle true 0x922c6a1202e))))))))
 (.cycle true 0x822c6a1242e)))
 (.cycle true 0xc228691202d))
 (.cycle true 0xb228691202d))
 (.cycle true 0xa22c691202d))
 (.cycle true 0x922c6a1202d))))))))
 (.cycle true 0x822c6a1242d)))

private theorem valid2 : check (core13 2) (fun _ => 0) trace2 = true := by decide +kernel

private noncomputable def trace3 : Trace :=
 (.branch 10
 (.branch 1
 (.cycle false 0xa62d283802d)
 (.branch 2
 (.cycle false 0xa62d283804d)
 (.branch 3
 (.cycle false 0xa62d283806d)
 (.branch 4
 (.cycle false 0xa62d283808d)
 (.branch 5
 (.cycle false 0xa62d28380ad)
 (.branch 6
 (.cycle false 0xa62d28380cd)
 (.branch 7
 (.branch 8
 (.branch 9
 (.branch 11
 (.branch 12
 (.branch 25
 (.branch 14
 (.cycle false 0xc5a9283802e)
 (.branch 15
 (.cycle false 0xc5a9283804e)
 (.branch 16
 (.cycle false 0xc5a9283806e)
 (.branch 17
 (.cycle false 0xc5a9283808e)
 (.branch 18
 (.cycle false 0xc5a928380ae)
 (.branch 19
 (.cycle false 0xc5a928380ce)
 (.branch 20
 (.branch 21
 (.branch 22
 (.branch 23
 (.cycle false 0xb6b1ca4a0e0)
 (.cycle true 0xa2246811c2e))
 (.cycle true 0x92286811c2e))
 (.cycle true 0x82286911c2e))
 (.cycle true 0x7228691202e))))))))
 (.branch 14
 (.branch 20
 (.cycle false 0x762d494002e)
 (.branch 21
 (.cycle false 0x862d493802e)
 (.branch 22
 (.cycle false 0x962d483802e)
 (.branch 23
 (.cycle false 0xa62d283802e)
 (.branch 24
 (.cycle false 0xb629283802e)
 (.branch 13
 (.branch 15
 (.branch 16
 (.branch 17
 (.branch 18
 (.branch 19
 (.branch 32
 (.branch 33
 (.cycle false 0x762d49400cf)
 (.branch 34
 (.cycle false 0x862d49380cf)
 (.branch 35
 (.cycle false 0x962d48380cf)
 (.branch 36
 (.cycle false 0xa62d28380cf)
 (.branch 37
 (.cycle false 0xb62928380cf)
 (.branch 38
 (.cycle false 0xc5a928380cf)
 (.branch 26
 (.cycle false 0xf338a418820)
 (.cycle true 0x71a4480b00f))))))))
 (.branch 33
 (.branch 27
 (.cycle false 0x762d494002f)
 (.branch 28
 (.cycle false 0x762d494004f)
 (.branch 29
 (.cycle false 0x762d494006f)
 (.branch 30
 (.cycle false 0x762d494008f)
 (.branch 31
 (.cycle false 0x762d49400af)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.cycle false 0xb7b1aa4a0e0)
 (.cycle true 0xc2246811c2f))
 (.cycle true 0xb2246811c2f))
 (.cycle true 0xa2246811c2f))
 (.cycle true 0x92286811c2f))
 (.cycle true 0x82286911c2f)))))))
 (.cycle true 0x71a8490a0cf)))
 (.cycle true 0x71a8490a0ce))
 (.cycle true 0x71a8490a0ae))
 (.cycle true 0x71a8490a08e))
 (.cycle true 0x7228490a06e))
 (.cycle true 0x7228690a04e))
 (.cycle true 0x71a4480b00e)))))))
 (.cycle true 0xc2246811c2e)))
 (.cycle true 0xc2246811c2d))
 (.cycle true 0xb2246811c2d))
 (.cycle true 0x92286811c2d))
 (.cycle true 0x82286911c2d))
 (.cycle true 0x7228691202d))))))))
 (.branch 0
 (.branch 1
 (.branch 7
 (.cycle false 0x762d494002d)
 (.branch 8
 (.cycle false 0x862d493802d)
 (.branch 9
 (.cycle false 0x962d483802d)
 (.branch 11
 (.cycle false 0xb629283802d)
 (.branch 12
 (.cycle false 0xc5a9283802d)
 (.branch 2
 (.branch 3
 (.branch 4
 (.branch 5
 (.branch 6
 (.branch 19
 (.branch 20
 (.cycle false 0x762d49400ce)
 (.branch 21
 (.cycle false 0x862d49380ce)
 (.branch 22
 (.cycle false 0x962d48380ce)
 (.branch 23
 (.cycle false 0xa62d28380ce)
 (.branch 24
 (.cycle false 0xb62928380ce)
 (.branch 25
 (.cycle false 0xc5a928380ce)
 (.branch 13
 (.cycle false 0xe334a418820)
 (.cycle true 0x71a4480b00e))))))))
 (.branch 20
 (.branch 14
 (.cycle false 0x762d494002e)
 (.branch 15
 (.cycle false 0x762d494004e)
 (.branch 16
 (.cycle false 0x762d494006e)
 (.branch 17
 (.cycle false 0x762d494008e)
 (.branch 18
 (.cycle false 0x762d49400ae)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 32
 (.branch 33
 (.cycle false 0x762d49400cf)
 (.branch 34
 (.cycle false 0x862d49380cf)
 (.branch 35
 (.cycle false 0x962d48380cf)
 (.branch 36
 (.cycle false 0xa62d28380cf)
 (.branch 37
 (.cycle false 0xb62928380cf)
 (.branch 38
 (.cycle false 0xc5a928380cf)
 (.branch 26
 (.cycle false 0xf334a418820)
 (.cycle true 0x71a4480b00f))))))))
 (.branch 33
 (.branch 27
 (.cycle false 0x762d494002f)
 (.branch 28
 (.cycle false 0x762d494004f)
 (.branch 29
 (.cycle false 0x762d494006f)
 (.branch 30
 (.cycle false 0x762d494008f)
 (.branch 31
 (.cycle false 0x762d49400af)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.cycle false 0xb7b1ca4a0e0)
 (.cycle true 0xc2246811c2f))
 (.cycle true 0xb2246811c2f))
 (.cycle true 0xa2246811c2f))
 (.cycle true 0x92286811c2f))
 (.cycle true 0x82286911c2f)))))))
 (.cycle true 0x71a8490a0cf)))
 (.cycle true 0xc2246811c2e))
 (.cycle true 0xb2246811c2e))
 (.cycle true 0xa2246811c2e))
 (.cycle true 0x92286811c2e))
 (.cycle true 0x82286911c2e)))))))
 (.cycle true 0x71a8490a0ce)))
 (.cycle true 0x71a8490a0cd))
 (.cycle true 0x71a8490a0ad))
 (.cycle true 0x71a8490a08d))
 (.cycle true 0x7228490a06d))
 (.cycle true 0x7228690a04d)))))))
 (.cycle true 0xa2246811c2d))
 (.cycle true 0xa1a0470b00d)))

private theorem valid3 : check (core13 3) (fun _ => 0) trace3 = true := by decide +kernel

private noncomputable def trace4 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.branch 3
 (.cycle false 0x3398a41002d)
 (.branch 4
 (.cycle false 0x4398a31002d)
 (.branch 5
 (.cycle false 0x5398831002d)
 (.branch 6
 (.cycle false 0x6394831002d)
 (.branch 7
 (.cycle false 0x7314831002d)
 (.branch 8
 (.cycle false 0x862d490082d)
 (.cycle true 0x81a8490b00d)))))))))
 (.branch 8
 (.branch 2
 (.cycle false 0x862d490044d)
 (.branch 3
 (.cycle false 0x862d490046d)
 (.branch 4
 (.cycle false 0x862d490048d)
 (.branch 5
 (.cycle false 0x862d49004ad)
 (.branch 6
 (.cycle false 0x862d49004cd)
 (.branch 7
 (.cycle false 0x862d49004ed)
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 23
 (.branch 14
 (.cycle false 0xa62d280082e)
 (.branch 15
 (.cycle false 0xa62d280044e)
 (.branch 16
 (.cycle false 0xa62d280046e)
 (.branch 17
 (.cycle false 0xa62d280048e)
 (.branch 18
 (.cycle false 0xa62d28004ae)
 (.branch 19
 (.cycle false 0xa62d28004ce)
 (.branch 20
 (.cycle false 0xa62d28004ee)
 (.branch 21
 (.branch 22
 (.branch 24
 (.branch 25
 (.branch 36
 (.branch 27
 (.cycle false 0xa62d280082f)
 (.branch 28
 (.cycle false 0xa62d280044f)
 (.branch 29
 (.cycle false 0xa62d280046f)
 (.branch 30
 (.cycle false 0xa62d280048f)
 (.branch 31
 (.cycle false 0xa62d28004af)
 (.branch 32
 (.cycle false 0xa62d28004cf)
 (.branch 33
 (.cycle false 0xa62d28004ef)
 (.branch 34
 (.branch 35
 (.cycle false 0xb731aa7a500)
 (.cycle true 0x922c6a1202f))
 (.cycle true 0x822c6a1242f)))))))))
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.cycle true 0xa22c691202f))
 (.cycle true 0xa1a4480b00f)))
 (.cycle true 0xc228691202e))
 (.cycle true 0xb228691202e))
 (.cycle true 0x922c6a1202e))
 (.cycle true 0x822c6a1242e)))))))))
 (.branch 13
 (.branch 14
 (.cycle false 0x1398a41880e)
 (.cycle true 0xa22c691202e))
 (.cycle true 0xa1a4480b00e)))
 (.cycle true 0xc228691202d))
 (.cycle true 0xb228691202d))
 (.cycle true 0xa22c691202d))
 (.cycle true 0x922c6a1202d))))))))
 (.cycle true 0x822c6a1242d)))

private theorem valid4 : check (core13 4) (fun _ => 0) trace4 = true := by decide +kernel

private noncomputable def trace5 : Trace :=
 (.branch 12
 (.branch 5
 (.cycle false 0xc59062080ad)
 (.branch 6
 (.cycle false 0xc59062080cd)
 (.branch 7
 (.cycle false 0xc59062080ed)
 (.branch 8
 (.cycle false 0xc590620810d)
 (.branch 9
 (.cycle false 0xc590620812d)
 (.branch 10
 (.cycle false 0xc590620814d)
 (.branch 1
 (.branch 2
 (.branch 3
 (.branch 4
 (.branch 11
 (.branch 25
 (.branch 18
 (.cycle false 0xc59062080ae)
 (.branch 19
 (.cycle false 0xc59062080ce)
 (.branch 20
 (.cycle false 0xc59062080ee)
 (.branch 21
 (.cycle false 0xc590620810e)
 (.branch 22
 (.cycle false 0xc590620812e)
 (.branch 23
 (.cycle false 0xc590620814e)
 (.branch 14
 (.branch 15
 (.branch 16
 (.branch 17
 (.cycle false 0x4731ab18820)
 (.cycle true 0x51a0470988e))
 (.cycle true 0x5220470986e))
 (.cycle true 0x5220670984e))
 (.cycle true 0x5220671182e))))))))
 (.branch 13
 (.branch 18
 (.branch 14
 (.cycle false 0x5525073002e)
 (.branch 15
 (.cycle false 0x5525073004e)
 (.branch 16
 (.cycle false 0x5525073006e)
 (.branch 17
 (.cycle false 0x5525073008e)
 (.branch 24
 (.cycle false 0xb61062080ae)
 (.branch 19
 (.branch 20
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 38
 (.branch 31
 (.cycle false 0xc59062080af)
 (.branch 32
 (.cycle false 0xc59062080cf)
 (.branch 33
 (.cycle false 0xc59062080ef)
 (.branch 34
 (.cycle false 0xc590620810f)
 (.branch 35
 (.cycle false 0xc590620812f)
 (.branch 36
 (.cycle false 0xc590620814f)
 (.branch 27
 (.branch 28
 (.branch 29
 (.branch 30
 (.cycle false 0x47b1ab18820)
 (.cycle true 0x51a0470988f))
 (.cycle true 0x5220470986f))
 (.cycle true 0x5220670984f))
 (.cycle true 0x5220671182f))))))))
 (.branch 26
 (.branch 31
 (.branch 27
 (.cycle false 0x5525073002f)
 (.branch 28
 (.cycle false 0x5525073004f)
 (.branch 29
 (.cycle false 0x5525073006f)
 (.branch 30
 (.cycle false 0x5525073008f)
 (.branch 37
 (.cycle false 0xb61062080af)
 (.branch 32
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xf53928398a0)
 (.cycle true 0xa21c661142f))
 (.cycle true 0x921c661142f))
 (.cycle true 0x821c661142f))
 (.cycle true 0x7220661142f))
 (.cycle true 0x6220671142f)))))))
 (.cycle true 0xc40ce2304af))
 (.cycle true 0xc388c12ac0f)))
 (.cycle true 0xa21c661142e))
 (.cycle true 0x921c661142e))
 (.cycle true 0x821c661142e))
 (.cycle true 0x7220661142e))
 (.cycle true 0x6220671142e)))))))
 (.cycle true 0xc40ce2304ae))
 (.cycle true 0xc388c12ac0e)))
 (.cycle true 0xb40ce2304ad))
 (.cycle true 0x51a0470988d))
 (.cycle true 0x5220470986d))
 (.cycle true 0x5220670984d))
 (.cycle true 0x5220671182d))))))))
 (.branch 0
 (.branch 5
 (.branch 1
 (.cycle false 0x5525073002d)
 (.branch 2
 (.cycle false 0x5525073004d)
 (.branch 3
 (.cycle false 0x5525073006d)
 (.branch 4
 (.cycle false 0x5525073008d)
 (.branch 11
 (.cycle false 0xb61062080ad)
 (.branch 6
 (.branch 7
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 23
 (.branch 14
 (.cycle false 0xa4a0e62802e)
 (.branch 15
 (.cycle false 0xa4a0e62804e)
 (.branch 16
 (.cycle false 0xa4a0e62806e)
 (.branch 17
 (.cycle false 0xa4a0e62808e)
 (.branch 24
 (.cycle false 0xb610620814e)
 (.branch 25
 (.cycle false 0xc590620814e)
 (.branch 13
 (.cycle false 0xe53528398a0)
 (.cycle true 0x138cc22ac0e))))))))
 (.branch 14
 (.branch 18
 (.cycle false 0x5525073002e)
 (.branch 19
 (.cycle false 0x6525072802e)
 (.branch 20
 (.cycle false 0x7525062802e)
 (.branch 21
 (.cycle false 0x8524e62802e)
 (.branch 22
 (.cycle false 0x9520e62802e)
 (.branch 15
 (.branch 16
 (.branch 17
 (.branch 24
 (.branch 25
 (.branch 38
 (.branch 31
 (.cycle false 0xc59062080af)
 (.branch 32
 (.cycle false 0xc59062080cf)
 (.branch 33
 (.cycle false 0xc59062080ef)
 (.branch 34
 (.cycle false 0xc590620810f)
 (.branch 35
 (.cycle false 0xc590620812f)
 (.branch 36
 (.cycle false 0xc590620814f)
 (.branch 27
 (.branch 28
 (.branch 29
 (.branch 30
 (.cycle false 0x47b1cb18820)
 (.cycle true 0x51a0470988f))
 (.cycle true 0x5220470986f))
 (.cycle true 0x5220670984f))
 (.cycle true 0x5220671182f))))))))
 (.branch 26
 (.branch 31
 (.branch 27
 (.cycle false 0x5525073002f)
 (.branch 28
 (.cycle false 0x5525073004f)
 (.branch 29
 (.cycle false 0x5525073006f)
 (.branch 30
 (.cycle false 0x5525073008f)
 (.branch 37
 (.cycle false 0xb61062080af)
 (.branch 32
 (.branch 33
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xf53528398a0)
 (.cycle true 0xa21c661142f))
 (.cycle true 0x921c661142f))
 (.cycle true 0x821c661142f))
 (.cycle true 0x7220661142f))
 (.cycle true 0x6220671142f)))))))
 (.cycle true 0xc40ce2304af))
 (.cycle true 0xc388c12ac0f)))
 (.cycle true 0xc40ce2304ae))
 (.cycle true 0xb40ce2304ae))
 (.cycle true 0x51a0470988e))
 (.cycle true 0x5220470986e))
 (.cycle true 0x5220670984e)))))))
 (.cycle true 0xa21c661142e)))
 (.cycle true 0xa21c661142d))
 (.cycle true 0x921c661142d))
 (.cycle true 0x821c661142d))
 (.cycle true 0x7220661142d))
 (.cycle true 0x6220671142d)))))))
 (.cycle true 0xc40ce2304ad))
 (.cycle true 0xc388c12ac0d)))

private theorem valid5 : check (core13 5) (fun _ => 0) trace5 = true := by decide +kernel

private noncomputable def trace6 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.branch 3
 (.cycle false 0x3398a41002d)
 (.branch 4
 (.cycle false 0x4398a31002d)
 (.branch 5
 (.cycle false 0x5398831002d)
 (.branch 6
 (.cycle false 0x6394831002d)
 (.branch 7
 (.cycle false 0x7314831002d)
 (.branch 8
 (.cycle false 0x862d490082d)
 (.cycle true 0x81a8490ac0d)))))))))
 (.branch 8
 (.branch 2
 (.cycle false 0x862d490044d)
 (.branch 3
 (.cycle false 0x862d490046d)
 (.branch 4
 (.cycle false 0x862d490048d)
 (.branch 5
 (.cycle false 0x862d49004ad)
 (.branch 6
 (.cycle false 0x862d49004cd)
 (.branch 7
 (.cycle false 0x862d49004ed)
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 24
 (.branch 14
 (.cycle false 0xb629280082e)
 (.branch 15
 (.cycle false 0xb629280044e)
 (.branch 16
 (.cycle false 0xb629280046e)
 (.branch 17
 (.cycle false 0xb629280048e)
 (.branch 18
 (.cycle false 0xb62928004ae)
 (.branch 19
 (.cycle false 0xb62928004ce)
 (.branch 20
 (.cycle false 0xb62928004ee)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 25
 (.branch 37
 (.branch 27
 (.cycle false 0xb629280082f)
 (.branch 28
 (.cycle false 0xb629280044f)
 (.branch 29
 (.cycle false 0xb629280046f)
 (.branch 30
 (.cycle false 0xb629280048f)
 (.branch 31
 (.cycle false 0xb62928004af)
 (.branch 32
 (.cycle false 0xb62928004cf)
 (.branch 33
 (.cycle false 0xb62928004ef)
 (.branch 34
 (.branch 35
 (.cycle false 0xa731ab7a500)
 (.cycle true 0x922c6a1202f))
 (.cycle true 0x822c6a1242f)))))))))
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.cycle true 0xb228691202f))
 (.cycle true 0xb1a4480b00f)))
 (.cycle true 0xc228691202e))
 (.cycle true 0xa22c691202e))
 (.cycle true 0x922c6a1202e))
 (.cycle true 0x822c6a1242e)))))))))
 (.branch 13
 (.branch 14
 (.cycle false 0x1398a41880e)
 (.cycle true 0xb228691202e))
 (.cycle true 0xb1a4480b00e)))
 (.cycle true 0xc228691202d))
 (.cycle true 0xb228691202d))
 (.cycle true 0xa22c691202d))
 (.cycle true 0x922c6a1202d))))))))
 (.cycle true 0x822c6a1242d)))

private theorem valid6 : check (core13 6) (fun _ => 0) trace6 = true := by decide +kernel

private noncomputable def trace7 : Trace :=
 (.branch 12
 (.branch 4
 (.cycle false 0xc5a8620808d)
 (.branch 5
 (.cycle false 0xc5a862080ad)
 (.branch 6
 (.cycle false 0xc5a862080cd)
 (.branch 7
 (.cycle false 0xc5a862080ed)
 (.branch 8
 (.cycle false 0xc5a8620810d)
 (.branch 9
 (.cycle false 0xc5a8620812d)
 (.branch 1
 (.branch 2
 (.branch 3
 (.branch 10
 (.branch 11
 (.branch 25
 (.branch 17
 (.cycle false 0xc5a8620808e)
 (.branch 18
 (.cycle false 0xc5a862080ae)
 (.branch 19
 (.cycle false 0xc5a862080ce)
 (.branch 20
 (.cycle false 0xc5a862080ee)
 (.branch 21
 (.cycle false 0xc5a8620810e)
 (.branch 22
 (.cycle false 0xc5a8620812e)
 (.branch 14
 (.branch 15
 (.branch 16
 (.cycle false 0x3731ab50820)
 (.cycle true 0x451c460946e))
 (.cycle true 0x451c660944e))
 (.cycle true 0x451c661142e))))))))
 (.branch 13
 (.branch 17
 (.branch 14
 (.cycle false 0x44a0e62802e)
 (.branch 15
 (.cycle false 0x44a0e62804e)
 (.branch 16
 (.cycle false 0x44a0e62806e)
 (.branch 23
 (.cycle false 0xa62c620808e)
 (.branch 24
 (.cycle false 0xb628620808e)
 (.branch 18
 (.branch 19
 (.branch 20
 (.branch 21
 (.branch 22
 (.branch 38
 (.branch 30
 (.cycle false 0xc5a8620808f)
 (.branch 31
 (.cycle false 0xc5a862080af)
 (.branch 32
 (.cycle false 0xc5a862080cf)
 (.branch 33
 (.cycle false 0xc5a862080ef)
 (.branch 34
 (.cycle false 0xc5a8620810f)
 (.branch 35
 (.cycle false 0xc5a8620812f)
 (.branch 27
 (.branch 28
 (.branch 29
 (.cycle false 0x37b1ab50820)
 (.cycle true 0x451c460946f))
 (.cycle true 0x451c660944f))
 (.cycle true 0x451c661142f))))))))
 (.branch 26
 (.branch 30
 (.branch 27
 (.cycle false 0x44a0e62802f)
 (.branch 28
 (.cycle false 0x44a0e62804f)
 (.branch 29
 (.cycle false 0x44a0e62806f)
 (.branch 36
 (.cycle false 0xa62c620808f)
 (.branch 37
 (.cycle false 0xb628620808f)
 (.branch 31
 (.branch 32
 (.branch 33
 (.branch 34
 (.branch 35
 (.cycle false 0xf4b90731480)
 (.cycle true 0x9518651102f))
 (.cycle true 0x8518651102f))
 (.cycle true 0x7518651102f))
 (.cycle true 0x651c651102f))
 (.cycle true 0x551c661102f)))))))
 (.cycle true 0xc38cc22848f))
 (.cycle true 0xc308a12280f)))
 (.cycle true 0x9518651102e))
 (.cycle true 0x8518651102e))
 (.cycle true 0x7518651102e))
 (.cycle true 0x651c651102e))
 (.cycle true 0x551c661102e)))))))
 (.cycle true 0xc38cc22848e))
 (.cycle true 0xc308a12280e)))
 (.cycle true 0xb38cc22848d))
 (.cycle true 0xa38cc22848d))
 (.cycle true 0x451c460946d))
 (.cycle true 0x451c660944d))
 (.cycle true 0x451c661142d))))))))
 (.branch 0
 (.branch 4
 (.branch 1
 (.cycle false 0x44a0e62802d)
 (.branch 2
 (.cycle false 0x44a0e62804d)
 (.branch 3
 (.cycle false 0x44a0e62806d)
 (.branch 10
 (.cycle false 0xa62c620808d)
 (.branch 11
 (.cycle false 0xb628620808d)
 (.branch 5
 (.branch 6
 (.branch 7
 (.branch 8
 (.branch 9
 (.branch 22
 (.branch 14
 (.cycle false 0x941cc52002e)
 (.branch 15
 (.cycle false 0x941cc52004e)
 (.branch 16
 (.cycle false 0x941cc52006e)
 (.branch 23
 (.cycle false 0xa62c620812e)
 (.branch 24
 (.cycle false 0xb628620812e)
 (.branch 25
 (.cycle false 0xc5a8620812e)
 (.branch 13
 (.cycle false 0xe4b50731480)
 (.cycle true 0x130ca22280e))))))))
 (.branch 14
 (.branch 17
 (.cycle false 0x44a0e62802e)
 (.branch 18
 (.cycle false 0x54a0e62002e)
 (.branch 19
 (.cycle false 0x64a0e52002e)
 (.branch 20
 (.cycle false 0x74a0c52002e)
 (.branch 21
 (.cycle false 0x849cc52002e)
 (.branch 15
 (.branch 16
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 38
 (.branch 30
 (.cycle false 0xc5a8620808f)
 (.branch 31
 (.cycle false 0xc5a862080af)
 (.branch 32
 (.cycle false 0xc5a862080cf)
 (.branch 33
 (.cycle false 0xc5a862080ef)
 (.branch 34
 (.cycle false 0xc5a8620810f)
 (.branch 35
 (.cycle false 0xc5a8620812f)
 (.branch 27
 (.branch 28
 (.branch 29
 (.cycle false 0x37b1cb50820)
 (.cycle true 0x451c460946f))
 (.cycle true 0x451c660944f))
 (.cycle true 0x451c661142f))))))))
 (.branch 26
 (.branch 30
 (.branch 27
 (.cycle false 0x44a0e62802f)
 (.branch 28
 (.cycle false 0x44a0e62804f)
 (.branch 29
 (.cycle false 0x44a0e62806f)
 (.branch 36
 (.cycle false 0xa62c620808f)
 (.branch 37
 (.cycle false 0xb628620808f)
 (.branch 31
 (.branch 32
 (.branch 33
 (.branch 34
 (.branch 35
 (.cycle false 0xf4b50731480)
 (.cycle true 0x9518651102f))
 (.cycle true 0x8518651102f))
 (.cycle true 0x7518651102f))
 (.cycle true 0x651c651102f))
 (.cycle true 0x551c661102f)))))))
 (.cycle true 0xc38cc22848f))
 (.cycle true 0xc308a12280f)))
 (.cycle true 0xc38cc22848e))
 (.cycle true 0xb38cc22848e))
 (.cycle true 0xa38cc22848e))
 (.cycle true 0x451c460946e))
 (.cycle true 0x451c660944e)))))))
 (.cycle true 0x9518651102e)))
 (.cycle true 0x9518651102d))
 (.cycle true 0x8518651102d))
 (.cycle true 0x7518651102d))
 (.cycle true 0x651c651102d))
 (.cycle true 0x551c661102d)))))))
 (.cycle true 0xc38cc22848d))
 (.cycle true 0xc308a12280d)))

private theorem valid7 : check (core13 7) (fun _ => 0) trace7 = true := by decide +kernel

private noncomputable def trace8 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.branch 3
 (.cycle false 0x3398a41002d)
 (.branch 4
 (.cycle false 0x4398a31002d)
 (.branch 5
 (.cycle false 0x5398831002d)
 (.branch 6
 (.cycle false 0x6394831002d)
 (.branch 7
 (.cycle false 0x7314831002d)
 (.branch 8
 (.cycle false 0x862d490082d)
 (.cycle true 0x81ac490a80d)))))))))
 (.branch 8
 (.branch 2
 (.cycle false 0x862d490044d)
 (.branch 3
 (.cycle false 0x862d490046d)
 (.branch 4
 (.cycle false 0x862d490048d)
 (.branch 5
 (.cycle false 0x862d49004ad)
 (.branch 6
 (.cycle false 0x862d49004cd)
 (.branch 7
 (.cycle false 0x862d49004ed)
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 24
 (.branch 14
 (.cycle false 0xb629280082e)
 (.branch 15
 (.cycle false 0xb629280044e)
 (.branch 16
 (.cycle false 0xb629280046e)
 (.branch 17
 (.cycle false 0xb629280048e)
 (.branch 18
 (.cycle false 0xb62928004ae)
 (.branch 19
 (.cycle false 0xb62928004ce)
 (.branch 20
 (.cycle false 0xb62928004ee)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 25
 (.branch 37
 (.branch 27
 (.cycle false 0xb629280082f)
 (.branch 28
 (.cycle false 0xb629280044f)
 (.branch 29
 (.cycle false 0xb629280046f)
 (.branch 30
 (.cycle false 0xb629280048f)
 (.branch 31
 (.cycle false 0xb62928004af)
 (.branch 32
 (.cycle false 0xb62928004cf)
 (.branch 33
 (.cycle false 0xb62928004ef)
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0x9731ab7a900)
 (.cycle true 0xa02c691202f))
 (.cycle true 0x91ac0a1202f))
 (.cycle true 0x81ac0a1242f)))))))))
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.cycle true 0xb028691202f))
 (.cycle true 0xb1a4480a80f)))
 (.cycle true 0xc028691202e))
 (.cycle true 0xa02c691202e))
 (.cycle true 0x91ac0a1202e))
 (.cycle true 0x81ac0a1242e)))))))))
 (.branch 13
 (.branch 14
 (.cycle false 0x1398a41880e)
 (.cycle true 0xb028691202e))
 (.cycle true 0xb1a4480a80e)))
 (.cycle true 0xc028691202d))
 (.cycle true 0xb028691202d))
 (.cycle true 0xa02c691202d))
 (.cycle true 0x91ac0a1202d))))))))
 (.cycle true 0x81ac0a1242d)))

private theorem valid8 : check (core13 8) (fun _ => 0) trace8 = true := by decide +kernel

private noncomputable def trace9 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.cycle true 0x250d2141c0d)))
 (.branch 0
 (.branch 2
 (.cycle false 0x2398a41840d)
 (.branch 3
 (.cycle false 0x3398a41040d)
 (.branch 4
 (.cycle false 0x4398a31040d)
 (.branch 5
 (.cycle false 0x5398831040d)
 (.branch 6
 (.cycle false 0x6394831040d)
 (.branch 7
 (.cycle false 0x7314831040d)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 14
 (.branch 13
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.cycle true 0x250d2141c0e)))
 (.branch 13
 (.branch 15
 (.cycle false 0x2398a41840e)
 (.branch 16
 (.cycle false 0x3398a41040e)
 (.branch 17
 (.cycle false 0x4398a31040e)
 (.branch 18
 (.cycle false 0x5398831040e)
 (.branch 19
 (.cycle false 0x6394831040e)
 (.branch 20
 (.cycle false 0x7314831040e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 37
 (.branch 27
 (.cycle false 0xb629280082f)
 (.branch 28
 (.cycle false 0xb629280044f)
 (.branch 29
 (.cycle false 0xb629280046f)
 (.branch 30
 (.cycle false 0xb629280048f)
 (.branch 31
 (.cycle false 0xb62928004af)
 (.branch 32
 (.cycle false 0xb62928004cf)
 (.branch 33
 (.cycle false 0xb62928004ef)
 (.branch 26
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xe6356f52500)
 (.cycle true 0xa22c691202f))
 (.cycle true 0x922c6a1202f))
 (.cycle true 0x822c6a1242f))
 (.cycle true 0x150d2241c0f)))))))))
 (.branch 27
 (.branch 26
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.cycle true 0x250d2141c0f)))
 (.cycle true 0xb228691202f)))
 (.cycle true 0xc228691202e))
 (.cycle true 0xb228691202e))
 (.cycle true 0xa22c691202e))
 (.cycle true 0x922c6a1202e))
 (.cycle true 0x822c6a1242e))))))))
 (.cycle true 0x150d2241c0e)))
 (.cycle true 0xc228691202d))
 (.cycle true 0xb228691202d))
 (.cycle true 0xa22c691202d))
 (.cycle true 0x922c6a1202d))
 (.cycle true 0x822c6a1242d))))))))
 (.cycle true 0x150d2241c0d)))

private theorem valid9 : check (core13 9) (fun _ => 0) trace9 = true := by decide +kernel

private noncomputable def trace10 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.cycle true 0x250d214180d)))
 (.branch 0
 (.branch 2
 (.cycle false 0x2398a41840d)
 (.branch 3
 (.cycle false 0x3398a41040d)
 (.branch 4
 (.cycle false 0x4398a31040d)
 (.branch 5
 (.cycle false 0x5398831040d)
 (.branch 6
 (.cycle false 0x6394831040d)
 (.branch 7
 (.cycle false 0x7314831040d)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 14
 (.branch 13
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.cycle true 0x250d214180e)))
 (.branch 13
 (.branch 15
 (.cycle false 0x2398a41840e)
 (.branch 16
 (.cycle false 0x3398a41040e)
 (.branch 17
 (.cycle false 0x4398a31040e)
 (.branch 18
 (.cycle false 0x5398831040e)
 (.branch 19
 (.cycle false 0x6394831040e)
 (.branch 20
 (.cycle false 0x7314831040e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 37
 (.branch 27
 (.cycle false 0xb629280082f)
 (.branch 28
 (.cycle false 0xb629280044f)
 (.branch 29
 (.cycle false 0xb629280046f)
 (.branch 30
 (.cycle false 0xb629280048f)
 (.branch 31
 (.cycle false 0xb62928004af)
 (.branch 32
 (.cycle false 0xb62928004cf)
 (.branch 33
 (.cycle false 0xb62928004ef)
 (.branch 26
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xe6356f52500)
 (.cycle true 0xa22c691202f))
 (.cycle true 0x922c6a1202f))
 (.cycle true 0x822c6a1242f))
 (.cycle true 0x150d224180f)))))))))
 (.branch 27
 (.branch 26
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.cycle true 0x250d214180f)))
 (.cycle true 0xb228691202f)))
 (.cycle true 0xc228691202e))
 (.cycle true 0xb228691202e))
 (.cycle true 0xa22c691202e))
 (.cycle true 0x922c6a1202e))
 (.cycle true 0x822c6a1242e))))))))
 (.cycle true 0x150d224180e)))
 (.cycle true 0xc228691202d))
 (.cycle true 0xb228691202d))
 (.cycle true 0xa22c691202d))
 (.cycle true 0x922c6a1202d))
 (.cycle true 0x822c6a1242d))))))))
 (.cycle true 0x150d224180d)))

private theorem valid10 : check (core13 10) (fun _ => 0) trace10 = true := by decide +kernel

private noncomputable def trace11 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.cycle true 0x250d214140d)))
 (.branch 0
 (.branch 2
 (.cycle false 0x2398a41840d)
 (.branch 3
 (.cycle false 0x3398a41040d)
 (.branch 4
 (.cycle false 0x4398a31040d)
 (.branch 5
 (.cycle false 0x5398831040d)
 (.branch 6
 (.cycle false 0x6394831040d)
 (.branch 7
 (.cycle false 0x7314831040d)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 14
 (.branch 13
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.cycle true 0x250d214140e)))
 (.branch 13
 (.branch 15
 (.cycle false 0x2398a41840e)
 (.branch 16
 (.cycle false 0x3398a41040e)
 (.branch 17
 (.cycle false 0x4398a31040e)
 (.branch 18
 (.cycle false 0x5398831040e)
 (.branch 19
 (.cycle false 0x6394831040e)
 (.branch 20
 (.cycle false 0x7314831040e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 37
 (.branch 27
 (.cycle false 0xb629280082f)
 (.branch 28
 (.cycle false 0xb629280044f)
 (.branch 29
 (.cycle false 0xb629280046f)
 (.branch 30
 (.cycle false 0xb629280048f)
 (.branch 31
 (.cycle false 0xb62928004af)
 (.branch 32
 (.cycle false 0xb62928004cf)
 (.branch 33
 (.cycle false 0xb62928004ef)
 (.branch 26
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xe6356f52500)
 (.cycle true 0xa22c691202f))
 (.cycle true 0x922c6a1202f))
 (.cycle true 0x822c6a1242f))
 (.cycle true 0x150d224140f)))))))))
 (.branch 27
 (.branch 26
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.cycle true 0x250d214140f)))
 (.cycle true 0xb228691202f)))
 (.cycle true 0xc228691202e))
 (.cycle true 0xb228691202e))
 (.cycle true 0xa22c691202e))
 (.cycle true 0x922c6a1202e))
 (.cycle true 0x822c6a1242e))))))))
 (.cycle true 0x150d224140e)))
 (.cycle true 0xc228691202d))
 (.cycle true 0xb228691202d))
 (.cycle true 0xa22c691202d))
 (.cycle true 0x922c6a1202d))
 (.cycle true 0x822c6a1242d))))))))
 (.cycle true 0x150d224140d)))

private theorem valid11 : check (core13 11) (fun _ => 0) trace11 = true := by decide +kernel

private noncomputable def trace12 : Trace :=
 (.branch 11
 (.branch 2
 (.cycle false 0xb629280804d)
 (.branch 3
 (.cycle false 0xb629280806d)
 (.branch 4
 (.cycle false 0xb629280808d)
 (.branch 5
 (.cycle false 0xb62928080ad)
 (.branch 6
 (.cycle false 0xb62928080cd)
 (.branch 7
 (.cycle false 0xb62928080ed)
 (.branch 1
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 12
 (.branch 24
 (.branch 15
 (.cycle false 0xb629280804e)
 (.branch 16
 (.cycle false 0xb629280806e)
 (.branch 17
 (.cycle false 0xb629280808e)
 (.branch 18
 (.cycle false 0xb62928080ae)
 (.branch 19
 (.cycle false 0xb62928080ce)
 (.branch 20
 (.cycle false 0xb62928080ee)
 (.branch 14
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 25
 (.branch 37
 (.branch 28
 (.cycle false 0xb629280804f)
 (.branch 29
 (.cycle false 0xb629280806f)
 (.branch 30
 (.cycle false 0xb629280808f)
 (.branch 31
 (.cycle false 0xb62928080af)
 (.branch 32
 (.cycle false 0xb62928080cf)
 (.branch 33
 (.cycle false 0xb62928080ef)
 (.branch 27
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xe6356f52501)
 (.cycle true 0xa224081844f))
 (.cycle true 0x9228081844f))
 (.cycle true 0x8228091844f))
 (.cycle true 0x25112040c2f))))))))
 (.branch 26
 (.branch 28
 (.branch 27
 (.cycle false 0x2398a41802f)
 (.branch 34
 (.cycle false 0x862d490804f)
 (.branch 35
 (.cycle false 0x962d480804f)
 (.branch 36
 (.cycle false 0xa62d280804f)
 (.branch 38
 (.cycle false 0xc5a9280804f)
 (.branch 29
 (.branch 30
 (.branch 31
 (.branch 32
 (.branch 33
 (.branch 50
 (.branch 41
 (.cycle false 0xb6292808050)
 (.branch 42
 (.cycle false 0xb6292808070)
 (.branch 43
 (.cycle false 0xb6292808090)
 (.branch 44
 (.cycle false 0xb62928080b0)
 (.branch 45
 (.cycle false 0xb62928080d0)
 (.branch 46
 (.cycle false 0xb62928080f0)
 (.branch 40
 (.branch 47
 (.branch 48
 (.branch 49
 (.cycle false 0xe6357052501)
 (.cycle true 0xa2240818450))
 (.cycle true 0x92280818450))
 (.cycle true 0x82280918450))
 (.cycle true 0x25112040c30))))))))
 (.branch 39
 (.branch 41
 (.branch 40
 (.cycle false 0x2398a418030)
 (.branch 47
 (.cycle false 0x862d4908050)
 (.branch 48
 (.cycle false 0x962d4808050)
 (.branch 49
 (.cycle false 0xa62d2808050)
 (.branch 51
 (.cycle false 0xc5a92808050)
 (.branch 42
 (.branch 43
 (.branch 44
 (.branch 45
 (.branch 46
 (.cycle false 0x103bcc520c40)
 (.cycle true 0x750d2040830))
 (.cycle true 0x650d2040830))
 (.cycle true 0x550d2040830))
 (.cycle true 0x450d2040830))
 (.cycle true 0x35112040830)))))))
 (.cycle true 0xb2240818450))
 (.cycle true 0xb2246112010)))
 (.cycle true 0x750d204082f))
 (.cycle true 0x650d204082f))
 (.cycle true 0x550d204082f))
 (.cycle true 0x450d204082f))
 (.cycle true 0x3511204082f)))))))
 (.cycle true 0xb224081844f))
 (.cycle true 0xb224611200f)))
 (.cycle true 0xc224081844e))
 (.cycle true 0xa224081844e))
 (.cycle true 0x9228081844e))
 (.cycle true 0x8228091844e))
 (.cycle true 0x25112040c2e))))))))
 (.branch 13
 (.branch 15
 (.branch 14
 (.cycle false 0x2398a41802e)
 (.branch 21
 (.cycle false 0x862d490804e)
 (.branch 22
 (.cycle false 0x962d480804e)
 (.branch 23
 (.cycle false 0xa62d280804e)
 (.branch 25
 (.cycle false 0xc5a9280804e)
 (.branch 16
 (.branch 17
 (.branch 18
 (.branch 19
 (.branch 20
 (.branch 33
 (.branch 27
 (.cycle false 0x7314831002f)
 (.branch 34
 (.cycle false 0x862d49080ef)
 (.branch 35
 (.cycle false 0x962d48080ef)
 (.branch 36
 (.cycle false 0xa62d28080ef)
 (.branch 37
 (.cycle false 0xb62928080ef)
 (.branch 38
 (.cycle false 0xc5a928080ef)
 (.branch 26
 (.cycle false 0xf3b8c520c40)
 (.cycle true 0x1228691200f))))))))
 (.branch 27
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.branch 29
 (.cycle false 0x3398a41002f)
 (.branch 30
 (.cycle false 0x4398a31002f)
 (.branch 31
 (.cycle false 0x5398831002f)
 (.branch 32
 (.cycle false 0x6394831002f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 50
 (.branch 41
 (.cycle false 0xb6292808050)
 (.branch 42
 (.cycle false 0xb6292808070)
 (.branch 43
 (.cycle false 0xb6292808090)
 (.branch 44
 (.cycle false 0xb62928080b0)
 (.branch 45
 (.cycle false 0xb62928080d0)
 (.branch 46
 (.cycle false 0xb62928080f0)
 (.branch 40
 (.branch 47
 (.branch 48
 (.branch 49
 (.cycle false 0xf6357052501)
 (.cycle true 0xa2240818450))
 (.cycle true 0x92280818450))
 (.cycle true 0x82280918450))
 (.cycle true 0x25112040c30))))))))
 (.branch 39
 (.branch 41
 (.branch 40
 (.cycle false 0x2398a418030)
 (.branch 47
 (.cycle false 0x862d4908050)
 (.branch 48
 (.cycle false 0x962d4808050)
 (.branch 49
 (.cycle false 0xa62d2808050)
 (.branch 51
 (.cycle false 0xc5a92808050)
 (.branch 42
 (.branch 43
 (.branch 44
 (.branch 45
 (.branch 46
 (.cycle false 0x103b8c520c40)
 (.cycle true 0x750d2040830))
 (.cycle true 0x650d2040830))
 (.cycle true 0x550d2040830))
 (.cycle true 0x450d2040830))
 (.cycle true 0x35112040830)))))))
 (.cycle true 0xb2240818450))
 (.cycle true 0xb2246112010)))
 (.cycle true 0xc224081844f))
 (.cycle true 0xb224081844f))
 (.cycle true 0xa224081844f))
 (.cycle true 0x9228081844f))
 (.cycle true 0x8228091844f)))))))
 (.cycle true 0x750d204082f)))
 (.cycle true 0x750d204082e))
 (.cycle true 0x650d204082e))
 (.cycle true 0x550d204082e))
 (.cycle true 0x450d204082e))
 (.cycle true 0x3511204082e)))))))
 (.cycle true 0xb224081844e))
 (.cycle true 0xb224611200e)))
 (.cycle true 0xc224081844d))
 (.cycle true 0xa224081844d))
 (.cycle true 0x9228081844d))
 (.cycle true 0x8228091844d))
 (.cycle true 0x25112040c2d))))))))
 (.branch 0
 (.branch 2
 (.branch 1
 (.cycle false 0x2398a41802d)
 (.branch 8
 (.cycle false 0x862d490804d)
 (.branch 9
 (.cycle false 0x962d480804d)
 (.branch 10
 (.cycle false 0xa62d280804d)
 (.branch 12
 (.cycle false 0xc5a9280804d)
 (.branch 3
 (.branch 4
 (.branch 5
 (.branch 6
 (.branch 7
 (.branch 20
 (.branch 14
 (.cycle false 0x7314831002e)
 (.branch 21
 (.cycle false 0x862d49080ee)
 (.branch 22
 (.cycle false 0x962d48080ee)
 (.branch 23
 (.cycle false 0xa62d28080ee)
 (.branch 24
 (.cycle false 0xb62928080ee)
 (.branch 25
 (.cycle false 0xc5a928080ee)
 (.branch 13
 (.cycle false 0xe3b4c520c40)
 (.cycle true 0x1228691200e))))))))
 (.branch 14
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.branch 16
 (.cycle false 0x3398a41002e)
 (.branch 17
 (.cycle false 0x4398a31002e)
 (.branch 18
 (.cycle false 0x5398831002e)
 (.branch 19
 (.cycle false 0x6394831002e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 33
 (.branch 27
 (.cycle false 0x7314831002f)
 (.branch 34
 (.cycle false 0x862d49080ef)
 (.branch 35
 (.cycle false 0x962d48080ef)
 (.branch 36
 (.cycle false 0xa62d28080ef)
 (.branch 37
 (.cycle false 0xb62928080ef)
 (.branch 38
 (.cycle false 0xc5a928080ef)
 (.branch 26
 (.cycle false 0xf3b4c520c40)
 (.cycle true 0x1228691200f))))))))
 (.branch 27
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.branch 29
 (.cycle false 0x3398a41002f)
 (.branch 30
 (.cycle false 0x4398a31002f)
 (.branch 31
 (.cycle false 0x5398831002f)
 (.branch 32
 (.cycle false 0x6394831002f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 50
 (.branch 41
 (.cycle false 0xb6292808050)
 (.branch 42
 (.cycle false 0xb6292808070)
 (.branch 43
 (.cycle false 0xb6292808090)
 (.branch 44
 (.cycle false 0xb62928080b0)
 (.branch 45
 (.cycle false 0xb62928080d0)
 (.branch 46
 (.cycle false 0xb62928080f0)
 (.branch 40
 (.branch 47
 (.branch 48
 (.branch 49
 (.cycle false 0xf6397052501)
 (.cycle true 0xa2240818450))
 (.cycle true 0x92280818450))
 (.cycle true 0x82280918450))
 (.cycle true 0x25112040c30))))))))
 (.branch 39
 (.branch 41
 (.branch 40
 (.cycle false 0x2398a418030)
 (.branch 47
 (.cycle false 0x862d4908050)
 (.branch 48
 (.cycle false 0x962d4808050)
 (.branch 49
 (.cycle false 0xa62d2808050)
 (.branch 51
 (.cycle false 0xc5a92808050)
 (.branch 42
 (.branch 43
 (.branch 44
 (.branch 45
 (.branch 46
 (.cycle false 0x103b4c520c40)
 (.cycle true 0x750d2040830))
 (.cycle true 0x650d2040830))
 (.cycle true 0x550d2040830))
 (.cycle true 0x450d2040830))
 (.cycle true 0x35112040830)))))))
 (.cycle true 0xb2240818450))
 (.cycle true 0xb2246112010)))
 (.cycle true 0xc224081844f))
 (.cycle true 0xb224081844f))
 (.cycle true 0xa224081844f))
 (.cycle true 0x9228081844f))
 (.cycle true 0x8228091844f)))))))
 (.cycle true 0x750d204082f)))
 (.cycle true 0xc224081844e))
 (.cycle true 0xb224081844e))
 (.cycle true 0xa224081844e))
 (.cycle true 0x9228081844e))
 (.cycle true 0x8228091844e)))))))
 (.cycle true 0x750d204082e)))
 (.cycle true 0x750d204082d))
 (.cycle true 0x650d204082d))
 (.cycle true 0x550d204082d))
 (.cycle true 0x450d204082d))
 (.cycle true 0x3511204082d)))))))
 (.cycle true 0xb224081844d))
 (.cycle true 0xb224611200d)))

private theorem valid12 : check (core13 12) (fun _ => 0) trace12 = true := by decide +kernel

private noncomputable def trace13 : Trace :=
 (.branch 0
 (.branch 1
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41840d)
 (.branch 3
 (.cycle false 0x3398a41040d)
 (.branch 4
 (.cycle false 0x4398a31040d)
 (.branch 5
 (.cycle false 0x5398831040d)
 (.branch 6
 (.cycle false 0x6394831040d)
 (.branch 7
 (.cycle false 0x7314831040d)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 13
 (.branch 14
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41840e)
 (.branch 16
 (.cycle false 0x3398a41040e)
 (.branch 17
 (.cycle false 0x4398a31040e)
 (.branch 18
 (.cycle false 0x5398831040e)
 (.branch 19
 (.cycle false 0x6394831040e)
 (.branch 20
 (.cycle false 0x7314831040e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41840f)
 (.branch 29
 (.cycle false 0x3398a41040f)
 (.branch 30
 (.cycle false 0x4398a31040f)
 (.branch 31
 (.cycle false 0x5398831040f)
 (.branch 32
 (.cycle false 0x6394831040f)
 (.branch 33
 (.cycle false 0x7314831040f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490202f))
 (.cycle true 0xb1a8490202f))
 (.cycle true 0xa1ac490202f))
 (.cycle true 0x91ac4a0202f))
 (.cycle true 0x81ac4a0242f)))))))))
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490a00f))
 (.cycle true 0xb1a8490a00f))
 (.cycle true 0xa1ac490a00f))
 (.cycle true 0x91ac4a0a00f))
 (.cycle true 0x81ac4a0a40f)))
 (.cycle true 0xc1a8490202e))
 (.cycle true 0xb1a8490202e))
 (.cycle true 0xa1ac490202e))
 (.cycle true 0x91ac4a0202e))
 (.cycle true 0x81ac4a0242e)))))))))
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41840f)
 (.branch 29
 (.cycle false 0x3398a41040f)
 (.branch 30
 (.cycle false 0x4398a31040f)
 (.branch 31
 (.cycle false 0x5398831040f)
 (.branch 32
 (.cycle false 0x6394831040f)
 (.branch 33
 (.cycle false 0x7314831040f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490202f))
 (.cycle true 0xb1a8490202f))
 (.cycle true 0xa1ac490202f))
 (.cycle true 0x91ac4a0202f))
 (.cycle true 0x81ac4a0242f)))))))))
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490a00f))
 (.cycle true 0xb1a8490a00f))
 (.cycle true 0xa1ac490a00f))
 (.cycle true 0x91ac4a0a00f))
 (.cycle true 0x81ac4a0a40f)))
 (.cycle true 0xc1a8490a00e))
 (.cycle true 0xb1a8490a00e))
 (.cycle true 0xa1ac490a00e))
 (.cycle true 0x91ac4a0a00e))
 (.cycle true 0x81ac4a0a40e)))
 (.cycle true 0xc1a8490202d))
 (.cycle true 0xb1a8490202d))
 (.cycle true 0xa1ac490202d))
 (.cycle true 0x91ac4a0202d))
 (.cycle true 0x81ac4a0242d)))))))))
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 13
 (.branch 14
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41840e)
 (.branch 16
 (.cycle false 0x3398a41040e)
 (.branch 17
 (.cycle false 0x4398a31040e)
 (.branch 18
 (.cycle false 0x5398831040e)
 (.branch 19
 (.cycle false 0x6394831040e)
 (.branch 20
 (.cycle false 0x7314831040e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41840f)
 (.branch 29
 (.cycle false 0x3398a41040f)
 (.branch 30
 (.cycle false 0x4398a31040f)
 (.branch 31
 (.cycle false 0x5398831040f)
 (.branch 32
 (.cycle false 0x6394831040f)
 (.branch 33
 (.cycle false 0x7314831040f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490202f))
 (.cycle true 0xb1a8490202f))
 (.cycle true 0xa1ac490202f))
 (.cycle true 0x91ac4a0202f))
 (.cycle true 0x81ac4a0242f)))))))))
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490a00f))
 (.cycle true 0xb1a8490a00f))
 (.cycle true 0xa1ac490a00f))
 (.cycle true 0x91ac4a0a00f))
 (.cycle true 0x81ac4a0a40f)))
 (.cycle true 0xc1a8490202e))
 (.cycle true 0xb1a8490202e))
 (.cycle true 0xa1ac490202e))
 (.cycle true 0x91ac4a0202e))
 (.cycle true 0x81ac4a0242e)))))))))
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41840f)
 (.branch 29
 (.cycle false 0x3398a41040f)
 (.branch 30
 (.cycle false 0x4398a31040f)
 (.branch 31
 (.cycle false 0x5398831040f)
 (.branch 32
 (.cycle false 0x6394831040f)
 (.branch 33
 (.cycle false 0x7314831040f)
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490202f))
 (.cycle true 0xb1a8490202f))
 (.cycle true 0xa1ac490202f))
 (.cycle true 0x91ac4a0202f))
 (.cycle true 0x81ac4a0242f)))))))))
 (.branch 34
 (.branch 35
 (.branch 36
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 50
 (.cycle false 0xf6397053528)
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xb1a84902030))
 (.cycle true 0xb1a8490a010)))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac4902030))
 (.cycle true 0xa1ac490a010)))
 (.cycle true 0xc1a8490a00f))
 (.cycle true 0xb1a8490a00f))
 (.cycle true 0xa1ac490a00f))
 (.cycle true 0x91ac4a0a00f))
 (.cycle true 0x81ac4a0a40f)))
 (.cycle true 0xc1a8490a00e))
 (.cycle true 0xb1a8490a00e))
 (.cycle true 0xa1ac490a00e))
 (.cycle true 0x91ac4a0a00e))
 (.cycle true 0x81ac4a0a40e)))
 (.cycle true 0xc1a8490a00d))
 (.cycle true 0xb1a8490a00d))
 (.cycle true 0xa1ac490a00d))
 (.cycle true 0x91ac4a0a00d))
 (.cycle true 0x81ac4a0a40d)))

private theorem valid13 : check (core13 13) (fun _ => 0) trace13 = true := by decide +kernel

private noncomputable def trace14 : Trace :=
 (.branch 3
 (.branch 0
 (.cycle false 0x3398a41040d)
 (.branch 1
 (.cycle false 0x3398a41002d)
 (.cycle true 0x15112240c0d)))
 (.branch 0
 (.branch 1
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41840d)
 (.branch 4
 (.cycle false 0x4398a31040d)
 (.branch 5
 (.cycle false 0x5398831040d)
 (.branch 6
 (.cycle false 0x6394831040d)
 (.branch 7
 (.cycle false 0x7314831040d)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 16
 (.branch 13
 (.cycle false 0x3398a41040e)
 (.branch 14
 (.cycle false 0x3398a41002e)
 (.cycle true 0x15112240c0e)))
 (.branch 13
 (.branch 14
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41840e)
 (.branch 17
 (.cycle false 0x4398a31040e)
 (.branch 18
 (.cycle false 0x5398831040e)
 (.branch 19
 (.cycle false 0x6394831040e)
 (.branch 20
 (.cycle false 0x7314831040e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 37
 (.branch 27
 (.cycle false 0xb629280082f)
 (.branch 28
 (.cycle false 0xb629280044f)
 (.branch 29
 (.cycle false 0xb629280046f)
 (.branch 30
 (.cycle false 0xb629280048f)
 (.branch 31
 (.cycle false 0xb62928004af)
 (.branch 32
 (.cycle false 0xb62928004cf)
 (.branch 33
 (.cycle false 0xb62928004ef)
 (.branch 26
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xe6356f52500)
 (.cycle true 0xa200691202f))
 (.cycle true 0x92006a1202f))
 (.cycle true 0x82006a1242f))
 (.cycle true 0x15112240c0f)))))))))
 (.branch 27
 (.branch 26
 (.cycle false 0x1398a41880f)
 (.branch 29
 (.cycle false 0x3398a41002f)
 (.cycle true 0x3509214100f)))
 (.cycle true 0xb200691202f)))
 (.cycle true 0xc200691202e))
 (.cycle true 0xb200691202e))
 (.cycle true 0xa200691202e))
 (.cycle true 0x92006a1202e))
 (.cycle true 0x82006a1242e))))))))
 (.cycle true 0x3509214100e)))
 (.cycle true 0xc200691202d))
 (.cycle true 0xb200691202d))
 (.cycle true 0xa200691202d))
 (.cycle true 0x92006a1202d))
 (.cycle true 0x82006a1242d))))))))
 (.cycle true 0x3509214100d)))

private theorem valid14 : check (core13 14) (fun _ => 0) trace14 = true := by decide +kernel

private noncomputable def trace15 : Trace :=
 (.branch 12
 (.branch 3
 (.cycle false 0xc5a9220806d)
 (.branch 4
 (.cycle false 0xc5a9220808d)
 (.branch 5
 (.cycle false 0xc5a922080ad)
 (.branch 6
 (.cycle false 0xc5a922080cd)
 (.branch 7
 (.cycle false 0xc5a922080ed)
 (.branch 8
 (.cycle false 0xc5a9220810d)
 (.branch 1
 (.branch 2
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 25
 (.branch 16
 (.cycle false 0xc5a9220806e)
 (.branch 17
 (.cycle false 0xc5a9220808e)
 (.branch 18
 (.cycle false 0xc5a922080ae)
 (.branch 19
 (.cycle false 0xc5a922080ce)
 (.branch 20
 (.cycle false 0xc5a922080ee)
 (.branch 21
 (.cycle false 0xc5a9220810e)
 (.branch 14
 (.branch 15
 (.cycle false 0x2731ab52420)
 (.cycle true 0x3501250904e))
 (.cycle true 0x3501251102e))))))))
 (.branch 13
 (.branch 16
 (.branch 14
 (.cycle false 0x341cc52002e)
 (.branch 15
 (.cycle false 0x341cc52004e)
 (.branch 22
 (.cycle false 0x962d420806e)
 (.branch 23
 (.cycle false 0xa62d220806e)
 (.branch 24
 (.cycle false 0xb629220806e)
 (.branch 17
 (.branch 18
 (.branch 19
 (.branch 20
 (.branch 21
 (.branch 38
 (.branch 29
 (.cycle false 0xc5a9220806f)
 (.branch 30
 (.cycle false 0xc5a9220808f)
 (.branch 31
 (.cycle false 0xc5a922080af)
 (.branch 32
 (.cycle false 0xc5a922080cf)
 (.branch 33
 (.cycle false 0xc5a922080ef)
 (.branch 34
 (.cycle false 0xc5a9220810f)
 (.branch 27
 (.branch 28
 (.cycle false 0x27b1ab52420)
 (.cycle true 0x3501250904f))
 (.cycle true 0x3501251102f))))))))
 (.branch 26
 (.branch 29
 (.branch 27
 (.cycle false 0x341cc52002f)
 (.branch 28
 (.cycle false 0x341cc52004f)
 (.branch 35
 (.cycle false 0x962d420806f)
 (.branch 36
 (.cycle false 0xa62d220806f)
 (.branch 37
 (.cycle false 0xb629220806f)
 (.branch 30
 (.branch 31
 (.branch 32
 (.branch 33
 (.branch 34
 (.cycle false 0xf438e629060)
 (.cycle true 0x85012410c2f))
 (.cycle true 0x75012410c2f))
 (.cycle true 0x65012410c2f))
 (.cycle true 0x55012410c2f))
 (.cycle true 0x45012510c2f)))))))
 (.cycle true 0xc024a22046f))
 (.cycle true 0xc288811a40f)))
 (.cycle true 0x85012410c2e))
 (.cycle true 0x75012410c2e))
 (.cycle true 0x65012410c2e))
 (.cycle true 0x55012410c2e))
 (.cycle true 0x45012510c2e)))))))
 (.cycle true 0xc024a22046e))
 (.cycle true 0xc288811a40e)))
 (.cycle true 0xb024a22046d))
 (.cycle true 0xa024a22046d))
 (.cycle true 0x9028a22046d))
 (.cycle true 0x3501250904d))
 (.cycle true 0x3501251102d))))))))
 (.branch 0
 (.branch 3
 (.branch 1
 (.cycle false 0x341cc52002d)
 (.branch 2
 (.cycle false 0x341cc52004d)
 (.branch 9
 (.cycle false 0x962d420806d)
 (.branch 10
 (.cycle false 0xa62d220806d)
 (.branch 11
 (.cycle false 0xb629220806d)
 (.branch 4
 (.branch 5
 (.branch 6
 (.branch 7
 (.branch 8
 (.branch 21
 (.branch 14
 (.cycle false 0x8398a41802e)
 (.branch 15
 (.cycle false 0x8398a41804e)
 (.branch 22
 (.cycle false 0x962d420810e)
 (.branch 23
 (.cycle false 0xa62d220810e)
 (.branch 24
 (.cycle false 0xb629220810e)
 (.branch 25
 (.cycle false 0xc5a9220810e)
 (.branch 13
 (.cycle false 0xe434e629060)
 (.cycle true 0x12a8821a40e))))))))
 (.branch 14
 (.branch 16
 (.cycle false 0x341cc52002e)
 (.branch 17
 (.cycle false 0x441cc51802e)
 (.branch 18
 (.cycle false 0x541cc41802e)
 (.branch 19
 (.cycle false 0x641ca41802e)
 (.branch 20
 (.cycle false 0x7418a41802e)
 (.branch 15
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 38
 (.branch 29
 (.cycle false 0xc5a9220806f)
 (.branch 30
 (.cycle false 0xc5a9220808f)
 (.branch 31
 (.cycle false 0xc5a922080af)
 (.branch 32
 (.cycle false 0xc5a922080cf)
 (.branch 33
 (.cycle false 0xc5a922080ef)
 (.branch 34
 (.cycle false 0xc5a9220810f)
 (.branch 27
 (.branch 28
 (.cycle false 0x27b1cb52420)
 (.cycle true 0x3501250904f))
 (.cycle true 0x3501251102f))))))))
 (.branch 26
 (.branch 29
 (.branch 27
 (.cycle false 0x341cc52002f)
 (.branch 28
 (.cycle false 0x341cc52004f)
 (.branch 35
 (.cycle false 0x962d420806f)
 (.branch 36
 (.cycle false 0xa62d220806f)
 (.branch 37
 (.cycle false 0xb629220806f)
 (.branch 30
 (.branch 31
 (.branch 32
 (.branch 33
 (.branch 34
 (.cycle false 0xf434e629060)
 (.cycle true 0x85012410c2f))
 (.cycle true 0x75012410c2f))
 (.cycle true 0x65012410c2f))
 (.cycle true 0x55012410c2f))
 (.cycle true 0x45012510c2f)))))))
 (.cycle true 0xc024a22046f))
 (.cycle true 0xc288811a40f)))
 (.cycle true 0xc024a22046e))
 (.cycle true 0xb024a22046e))
 (.cycle true 0xa024a22046e))
 (.cycle true 0x9028a22046e))
 (.cycle true 0x3501250904e)))))))
 (.cycle true 0x85012410c2e)))
 (.cycle true 0x85012410c2d))
 (.cycle true 0x75012410c2d))
 (.cycle true 0x65012410c2d))
 (.cycle true 0x55012410c2d))
 (.cycle true 0x45012510c2d)))))))
 (.cycle true 0xc024a22046d))
 (.cycle true 0xc288811a40d)))

private theorem valid15 : check (core13 15) (fun _ => 0) trace15 = true := by decide +kernel

private noncomputable def trace16 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.branch 3
 (.cycle false 0x3398a41002d)
 (.branch 4
 (.cycle false 0x4398a31002d)
 (.branch 5
 (.cycle false 0x5398831002d)
 (.branch 6
 (.cycle false 0x6394831002d)
 (.branch 7
 (.cycle false 0x7314831002d)
 (.branch 8
 (.cycle false 0x8018a41882d)
 (.cycle true 0x81ac4a0a40d)))))))))
 (.branch 8
 (.branch 2
 (.cycle false 0x8018a41844d)
 (.branch 3
 (.cycle false 0x8018a41046d)
 (.branch 4
 (.cycle false 0x8018a31048d)
 (.branch 5
 (.cycle false 0x801883104ad)
 (.branch 6
 (.cycle false 0x801483104cd)
 (.branch 7
 (.cycle false 0x801483104ed)
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 14
 (.branch 13
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.branch 16
 (.cycle false 0x3398a41002e)
 (.branch 17
 (.cycle false 0x4398a31002e)
 (.branch 18
 (.cycle false 0x5398831002e)
 (.branch 19
 (.cycle false 0x6394831002e)
 (.branch 20
 (.cycle false 0x7314831002e)
 (.branch 21
 (.cycle false 0x8018a41882e)
 (.cycle true 0x81ac4a0a40e)))))))))
 (.branch 21
 (.branch 15
 (.cycle false 0x8018a41844e)
 (.branch 16
 (.cycle false 0x8018a41046e)
 (.branch 17
 (.cycle false 0x8018a31048e)
 (.branch 18
 (.cycle false 0x801883104ae)
 (.branch 19
 (.cycle false 0x801483104ce)
 (.branch 20
 (.cycle false 0x801483104ee)
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 36
 (.branch 27
 (.cycle false 0xa62d280082f)
 (.branch 28
 (.cycle false 0xa62d280044f)
 (.branch 29
 (.cycle false 0xa62d280046f)
 (.branch 30
 (.cycle false 0xa62d280048f)
 (.branch 31
 (.cycle false 0xa62d28004af)
 (.branch 32
 (.cycle false 0xa62d28004cf)
 (.branch 33
 (.cycle false 0xa62d28004ef)
 (.branch 34
 (.branch 35
 (.branch 37
 (.branch 38
 (.branch 49
 (.branch 40
 (.cycle false 0xa62d2800830)
 (.branch 41
 (.cycle false 0xa62d2800450)
 (.branch 42
 (.cycle false 0xa62d2800470)
 (.branch 43
 (.cycle false 0xa62d2800490)
 (.branch 44
 (.cycle false 0xa62d28004b0)
 (.branch 45
 (.cycle false 0xa62d28004d0)
 (.branch 46
 (.cycle false 0xa62d28004f0)
 (.branch 47
 (.branch 48
 (.cycle false 0xf6396d54128)
 (.cycle true 0x91ac0a12030))
 (.cycle true 0x81ac4a02430)))))))))
 (.branch 39
 (.branch 40
 (.cycle false 0x1398a418810)
 (.cycle true 0xa1ac0912030))
 (.cycle true 0xa1ac480a410)))
 (.cycle true 0xc1a8091202f))
 (.cycle true 0xb1a8091202f))
 (.cycle true 0x91ac0a1202f))
 (.cycle true 0x81ac4a0242f)))))))))
 (.branch 26
 (.branch 27
 (.cycle false 0x1398a41880f)
 (.cycle true 0xa1ac091202f))
 (.cycle true 0xa1ac480a40f)))
 (.cycle true 0xc1a8091202e))
 (.cycle true 0xb1a8091202e))
 (.cycle true 0xa1ac091202e))
 (.cycle true 0x91ac0a1202e))))))))
 (.cycle true 0x81ac4a0242e)))
 (.cycle true 0xc1a8091202d))
 (.cycle true 0xb1a8091202d))
 (.cycle true 0xa1ac091202d))
 (.cycle true 0x91ac0a1202d))))))))
 (.cycle true 0x81ac4a0242d)))

private theorem valid16 : check (core13 16) (fun _ => 0) trace16 = true := by decide +kernel

private noncomputable def trace17 : Trace :=
 (.branch 1
 (.branch 0
 (.cycle false 0x1398a41880d)
 (.branch 2
 (.cycle false 0x2398a41802d)
 (.cycle true 0x250d214100d)))
 (.branch 0
 (.branch 2
 (.cycle false 0x2398a41840d)
 (.branch 3
 (.cycle false 0x3398a41040d)
 (.branch 4
 (.cycle false 0x4398a31040d)
 (.branch 5
 (.cycle false 0x5398831040d)
 (.branch 6
 (.cycle false 0x6394831040d)
 (.branch 7
 (.cycle false 0x7314831040d)
 (.branch 8
 (.branch 9
 (.branch 10
 (.branch 11
 (.branch 12
 (.branch 14
 (.branch 13
 (.cycle false 0x1398a41880e)
 (.branch 15
 (.cycle false 0x2398a41802e)
 (.cycle true 0x250d214100e)))
 (.branch 13
 (.branch 15
 (.cycle false 0x2398a41840e)
 (.branch 16
 (.cycle false 0x3398a41040e)
 (.branch 17
 (.cycle false 0x4398a31040e)
 (.branch 18
 (.cycle false 0x5398831040e)
 (.branch 19
 (.cycle false 0x6394831040e)
 (.branch 20
 (.cycle false 0x7314831040e)
 (.branch 21
 (.branch 22
 (.branch 23
 (.branch 24
 (.branch 25
 (.branch 37
 (.branch 27
 (.cycle false 0xb629280082f)
 (.branch 28
 (.cycle false 0xb629280044f)
 (.branch 29
 (.cycle false 0xb629280046f)
 (.branch 30
 (.cycle false 0xb629280048f)
 (.branch 31
 (.cycle false 0xb62928004af)
 (.branch 32
 (.cycle false 0xb62928004cf)
 (.branch 33
 (.cycle false 0xb62928004ef)
 (.branch 26
 (.branch 34
 (.branch 35
 (.branch 36
 (.cycle false 0xe6356f52500)
 (.cycle true 0xa22c691202f))
 (.cycle true 0x922c6a1202f))
 (.cycle true 0x822c6a1242f))
 (.cycle true 0x150d224100f)))))))))
 (.branch 27
 (.branch 26
 (.cycle false 0x1398a41880f)
 (.branch 28
 (.cycle false 0x2398a41802f)
 (.cycle true 0x250d214100f)))
 (.cycle true 0xb228691202f)))
 (.cycle true 0xc228691202e))
 (.cycle true 0xb228691202e))
 (.cycle true 0xa22c691202e))
 (.cycle true 0x922c6a1202e))
 (.cycle true 0x822c6a1242e))))))))
 (.cycle true 0x150d224100e)))
 (.cycle true 0xc228691202d))
 (.cycle true 0xb228691202d))
 (.cycle true 0xa22c691202d))
 (.cycle true 0x922c6a1202d))
 (.cycle true 0x822c6a1242d))))))))
 (.cycle true 0x150d224100d)))

private theorem valid17 : check (core13 17) (fun _ => 0) trace17 = true := by decide +kernel

/-- Every coloring of the spokes closes a monochromatic nine-cycle in one
of the eighteen possible colorings of the thirteen-vertex clique. -/
theorem eliminate_core {n} (c : Coloring n) (v : Fin 17 → Fin n) (color : Bool → Fin 3)
    (inj : ∀ ⦃i j⦄, v i=v j → i=j) (q : Fin 18)
    (base : ∀ i j : Fin 17, i.val<13 → j.val<13 → i≠j →
      c.edge (v i) (v j)=color (Cert16.edge (core13 q) i.val j.val))
    (spokes : ∀ i j : Fin 17, i.val<13 → 13 ≤ j.val →
      c.edge (v i) (v j)=color false ∨ c.edge (v i) (v j)=color true) : HasMonoC9 c := by
  have cases : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 ∨ q=6 ∨ q=7 ∨ q=8 ∨ q=9 ∨ q=10 ∨ q=11 ∨ q=12 ∨ q=13 ∨ q=14 ∨ q=15 ∨ q=16 ∨ q=17 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact trace_sound c v color (@inj) _ base spokes trace0 valid0
  · exact trace_sound c v color (@inj) _ base spokes trace1 valid1
  · exact trace_sound c v color (@inj) _ base spokes trace2 valid2
  · exact trace_sound c v color (@inj) _ base spokes trace3 valid3
  · exact trace_sound c v color (@inj) _ base spokes trace4 valid4
  · exact trace_sound c v color (@inj) _ base spokes trace5 valid5
  · exact trace_sound c v color (@inj) _ base spokes trace6 valid6
  · exact trace_sound c v color (@inj) _ base spokes trace7 valid7
  · exact trace_sound c v color (@inj) _ base spokes trace8 valid8
  · exact trace_sound c v color (@inj) _ base spokes trace9 valid9
  · exact trace_sound c v color (@inj) _ base spokes trace10 valid10
  · exact trace_sound c v color (@inj) _ base spokes trace11 valid11
  · exact trace_sound c v color (@inj) _ base spokes trace12 valid12
  · exact trace_sound c v color (@inj) _ base spokes trace13 valid13
  · exact trace_sound c v color (@inj) _ base spokes trace14 valid14
  · exact trace_sound c v color (@inj) _ base spokes trace15 valid15
  · exact trace_sound c v color (@inj) _ base spokes trace16 valid16
  · exact trace_sound c v color (@inj) _ base spokes trace17 valid17

end Ramsey556.Split17
