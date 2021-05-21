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

H = ∃ j, j => (while(true) l += 1)
∀ n m, H ∗ (l ↦ n) -∗ |==> H ∗ (l ↦ n + m)

k => (if(l == 3) if(l == 8) if(l == 12) crash)
-∗ |==>
k => crash

{P} e {ERR: Q} := ∀ j, P ∗ j => e -∗ |==> Q ∗ j => crash

{P} e {v. Q v} := ∀ mQ v ∗ j => e -∗ |==> P ∗ (j => v)


{{ l ↦ v }} store l v' {{ r, ⌜ r = VUnit ⌝ ∗ l ↦ v' }}.
{{ emp }} EAmb {{ v, ⌜ v = VNat n ⌝ }}.


post e P v
j => e
-----------
|==> P ∗ j => v



post e P v := ∀ j, j => e -∗ |==> P ∗ j => v

(l ↦ v')
-----------
post (store l v') (l ↦ v) VUnit.

(l ↦ v')
j => (store l v')
-----------
(l ↦ v) ∗ j => VUnit

