import Cat.STLCI.Stx

namespace STLC

def Ty.show (ty : Ty) : String :=
  match ty with
  | .arr t1 t2 => s!"({Ty.show t1} → {Ty.show t2})"
  | .unit => "1"
  | .prod t1 t2 => s!"({Ty.show t1} × {Ty.show t2})"



