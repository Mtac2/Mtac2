Require Import Mtac2.Base.
Import M.

Goal eval (isLambda (fun x:nat=>x)) = true. reflexivity. Qed.

Goal eval (isProd (forall x:nat, True)) = true. reflexivity. Qed.

Goal eval (isCast (True : Prop)) = true. reflexivity. Qed.

Goal eval (isApp (id 0)) = true. reflexivity. Qed.

Goal eval (isConst (@id)) = true. reflexivity. Qed.

Goal eval (isConstruct S) = true. reflexivity. Qed.
