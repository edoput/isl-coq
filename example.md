b := true
fork {
  while (load b):
    v := load v + 1
}
b := false
if load v == 99:
  if load v == 102:
    crash


j => e
l ↦ v

j => K[load l] ∗ l ↦ v -∗ |==> j => K[v] ∗ l ↦ v
j => K[store l v'] ∗ l ↦ v -∗ |==> j => K[()] ∗ l ↦ v'
j => K[fork e] -∗ |==> j => K[()] ∗ ∃ j', j' => e

j => K[crash] -∗ |==> False

post e P v := ∀ j K, j => K[e] -∗ |==> P ∗ j => K[v]


(l ↦ v')
--------
post (store l v') (l ↦ v) ().


(l ↦ v')
j => K[(store l v')]
--------
|==> (l ↦ v) ∗ j => K[v]


(l ↦ v')
j => K[(store l v')]
--------
|==> (l ↦ v) ∗ j => K[v]




(l ↦ v') ⊢ post (EStore (EVal (VLoc l)) (EVal v')) (l ↦ v) (Some VUnit).
