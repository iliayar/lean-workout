
-- HW 3 (2.4.a)
example : ((α → β) → α) → (α → α → β) → β :=
  fun f g => g (f (fun x => g x x)) (f (fun x => g x x))
example : ((α → β) → α) → (α → α → β) → β :=
  fun f g => g (f (fun x => g (f (fun x => g x x)) x)) (f (fun x => g x x))

-- HW 3 (2.4.b)
example : ((((α → β) → α) → α) → β) → β :=
  fun f => f fun g =>
    g fun x => f fun g' => x

example : ((((α → β) → α) → α) → β) → β :=
  fun f => f fun g => 
    g fun x => f fun g' => 
      g' fun x' => f fun g'' => x'

example : ((((α → β) → α) → α) → β) → β :=
  fun f => f fun g => 
    g fun x => f fun g' => 
      g' fun x' => f fun g'' =>
        g'' fun x'' => f fun g''' => x''

