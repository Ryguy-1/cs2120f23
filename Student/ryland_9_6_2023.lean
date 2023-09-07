

def is_even := (λ a => a % 2 == 0)
def add_two := (fun a => a+2)

#eval is_even 3
#eval add_two 2

def is_even_after_add_two := is_even ∘ add_two

#eval is_even_after_add_two 4
#check is_even_after_add_two


def composed_function := (λ a => a % 2 == 0) ∘ (fun a => a + 3)
#check composed_function

#eval composed_function 3