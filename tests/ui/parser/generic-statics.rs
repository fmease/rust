static S<T>: i32 = 0;
//~^ ERROR static items may not have generic parameters

static T: () = ()
where
    Vec<()>: Clone;
//~^^ ERROR static items may not have a where clause

static U: bool
where
    (): Copy,
= true;
//~^^^ ERROR static items may not have a where clause

fn main() {}
