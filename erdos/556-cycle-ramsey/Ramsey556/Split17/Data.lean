import Ramsey556.Cert16.Basic

namespace Ramsey556.Split17

private def graphs14 : Vector Nat 14 := #v[
  0x7e03e03c07018080fffffff, 0x7c03e03c07018080fffffff, 0x7c03c03c07018080fffffff,
  0x7c03c03807018080fffffff, 0x7e03f03e0781c0c081fffff, 0x7e03e03e0781c0c081fffff,
  0x7e03e03c0781c0c081fffff, 0x5556aaaaad5555aaab556ad, 0x5552aaaaad5555aaab556ad,
  0x2aaaaaaaad5555aaab556ad, 0x5542aaaaad5555aaab556ad, 0x2aa2aaaaad5555aaab556ad,
  0x5502aaaaad5555aaab556ad, 0x2a82aaaaad5555aaab556ad]

private def graphs13 : Vector Nat 18 := #v[
  0x3f07e1f8fcfc0410894, 0x1fc3f8fe7f7ffe00000, 0x3f87f1fcfefe0000000,
  0x1fc3f0fc7e7efc00000, 0x3fc7f1fcfefe0000000, 0x1f87f083c1e1e3cf7800,
  0x3fc7f9fcfefe0000000, 0xfc5f8fe20e0e1c73b80, 0x3fc7f9fefefe0000000,
  0x3f87f1fcfefe0200000, 0x3f87f1fcfefe0208000, 0x3f87f1fcfefe0208400,
  0x3f47e9fafdfd0410894, 0x3fc7f9feffff0000000, 0x3f87f1fcfefe0208448,
  0x7e4fcbf3f9060c319b0, 0x3fc7f9fefffe0000000, 0x3f87f1fcfefe0208440]

def core14 (q : Fin 14) := graphs14[q]

def core13 (q : Fin 18) := graphs13[q]

end Ramsey556.Split17
