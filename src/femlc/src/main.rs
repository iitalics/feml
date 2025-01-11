fn main() {
    static INPUT: &str = "
data (==) [A : type] (a : A) : A -> type {
  refl : a == a;
};

def sym (p : x == y) : y == x = match p {
  relf => refl;
};

def (+) (n : nat) (m : nat) : nat = match n {
  Z => m;
  S n' => S (n' + m);
};

";

    for tk in feml::token::Tokenizer::new(INPUT) {
        let (loc, tk) = tk.unwrap();
        println!("input:{loc}: {tk} {tk:?}");
    }
}
