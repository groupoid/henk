use std::collections::{HashMap, HashSet};
use std::fmt::{self, write, Debug, Display};
use std::hash::Hash;

use log::debug;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Henk {
    Universe(i64),
    Variable(String),
    App(Box<Henk>, Box<Henk>),
    Lambda(String, Box<Henk>, Box<Henk>),
    Forall(String, Box<Henk>, Box<Henk>),
}

impl Henk {

    pub fn type_check(self) -> Result<Henk, String> {
        println!("AUT-68: {}", self);
        self.type_check_with_context(HashMap::new())
    }

    pub fn type_check_with_context(self, context: HashMap<String, Henk>) -> Result<Henk, String> {
//      println!("Context: {:?}", context);
        match self {
            Henk::Universe(n) => Ok(Henk::Universe(n + 1)),
            Henk::Forall(bound, left, right) => { Ok(Henk::Universe(0)) }
            Henk::Variable(v) => match context.get(&v) { Some(ty) => Ok(ty.clone()), None => Err(format!("Cannot find variable {}.", &v)), },
            Henk::App(left, right) => {
                match left.type_check_with_context(context.clone())? {
                    Henk::Forall(bound, ty_in, ty_out) => {
                        let right_ty = right.clone().type_check_with_context(context.clone())?;
                        if right_ty.clone().nf().alpha_eq(&ty_in.clone().nf()) { Ok(ty_out.subst(&bound, &right)) }
                        else { Err(format!("Expected something of type {}, found that of type {}.", ty_in, right_ty), ) }
                    }
                    left_ty => { Err(format!("Expected lambda, found value of type {}.", left_ty.nf())) }
                }
            }
            Henk::Lambda(bound, left, right) => {
                let left_type = left.clone().type_check_with_context(context.clone())?;
                let mut new_context = context;
                new_context.insert(bound.clone(), *left.clone());
                let right_type = right.type_check_with_context(new_context)?;
                Ok(Henk::Forall(bound, left, Box::new(right_type)))
            }
        }
    }

    pub fn free_vars(&self) -> HashSet<&String> {
        fn  closure_vars<'a>(bound: &'a String, left: &'a Box<Henk>, right: &'a Box<Henk>) -> HashSet<&'a String> {
            let mut tmp = right.free_vars();
            tmp.remove(bound);
            tmp.union(&left.free_vars()).cloned().collect()
        }
        let mut set = HashSet::new();
        match *self {
            Henk::Universe(v) => {}
            Henk::Variable(ref v) => { set = HashSet::new(); set.insert(v); }
            Henk::App(ref left, ref right) => { set = left.free_vars().union(&right.free_vars()).cloned().collect() }
            Henk::Lambda(ref bound, ref left, ref right) => { closure_vars(bound, left, right); }
            Henk::Forall(ref bound, ref left, ref right) => { closure_vars(bound, left, right); }
        }
        set
    }

    pub fn subst(self, from: &String, to: &Henk) -> Henk {
        fn lambda(bound: String, left: Box<Henk>, right: Box<Henk>) -> Henk { Henk::Lambda(bound, left, right) }
        fn forall(bound: String, left: Box<Henk>, right: Box<Henk>) -> Henk { Henk::Forall(bound, left, right) }
        fn substitute_closure<'a>(from: &String, to: &Henk, bound: &'a String, left: &'a Box<Henk>, right: &'a Box<Henk>,
           fun: fn (bound: String, left: Box<Henk>, right: Box<Henk>) -> Henk) -> Henk {
            if bound == from { fun(bound.clone(),Box::new(left.clone().subst(from, to)),right.clone(),) }
            else {
                if !to.free_vars().contains(bound) { fun(bound.clone(), Box::new(left.clone().subst(from, to)), Box::new(right.clone().subst(from, to)),) }
                else {
                    let mut unused: String = bound.clone(); unused.push_str("'");
                    loop {
                        let used: HashSet<&String> = right.free_vars().union(&to.free_vars()).cloned().collect();
                        if used.contains(&unused) { unused.push_str("'") }
                        else {
                            return fun(unused.clone(), Box::new(left.clone().subst(bound, &Henk::Variable(unused.clone()), )),
                                Box::new(right.clone().subst(bound, &Henk::Variable(unused)), ), ).subst(from, to);
                        }
                    }
                }
            }
        }
        match self {
            Henk::Universe(v) => Henk::Universe(v),
            Henk::Variable(v) => { if v == *from { to.clone() } else { Henk::Variable(v) } }
            Henk::App(left, right) => { Henk::App(Box::new(left.subst(from, to)), Box::new(right.subst(from, to))) }
            Henk::Lambda(ref bound, ref left, ref right) => {  substitute_closure(from, to, bound, left, right, lambda) }
            Henk::Forall(ref bound, ref left, ref right) => {  substitute_closure(from, to, bound, left, right, forall) }
        }
    }

    pub fn nf(self) -> Henk {
        fn spine(leftmost: Henk, stack: &[Henk]) -> Henk {
            match (leftmost, stack) {
                (Henk::App(left, right), _) => { let mut new_stack: Vec<Henk> = stack.into(); new_stack.push(*right); spine(*left, &new_stack) }
                (Henk::Lambda(ref from, ref l, ref r), ref stack) if stack.is_empty() => { Henk::Lambda(from.clone(), Box::new(l.clone().nf()), Box::new(r.clone().nf()), ) }
                (Henk::Lambda(ref from, _, ref r), ref stack) => { let mut ns: Vec<Henk> = (*stack).into(); let right = ns.pop().unwrap(); spine(r.clone().subst(&from, &right), &ns) }
                (Henk::Forall(ref b, ref l, ref r), ref stack) => stack.iter().fold(Henk::Forall(b.clone(), Box::new(l.clone().nf()), Box::new(r.clone().nf()), ), |x, y| Henk::App(Box::new(x), Box::new(y.clone().nf()))),
                (leftmost, _) => stack.iter().fold(leftmost, |l, r| Henk::App(Box::new(l), Box::new(r.clone().nf())) ),
            }
        }
        spine(self, &[])
    }

    pub fn alpha_eq(&self, another: &Henk) -> bool {
        match (self, another) {
            (&Henk::Universe(v1), &Henk::Universe(v2)) => v1 == v2,
            (&Henk::Variable(ref v1), &Henk::Variable(ref v2)) => v1 == v2,
            (&Henk::App(ref left1, ref right1),&Henk::App(ref left2, ref right2),) => left1.alpha_eq(&left2) && right1.alpha_eq(&right2),
            (&Henk::Lambda(ref b1, ref l1, ref r1), &Henk::Lambda(ref b2, ref l2, ref r2),) => { l1.alpha_eq(l2) && r1.alpha_eq(&r2.clone().subst(&b2, &Henk::Variable(b1.clone())),) }
            (&Henk::Forall(ref b1, ref l1, ref r1), &Henk::Forall(ref b2, ref l2, ref r2),) => { l1.alpha_eq(l2) && r1.alpha_eq(&r2.clone().subst(&b2, &Henk::Variable(b1.clone())),) }
            _ => false,
        }
    }
}

impl Display for Henk {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Henk::*;
        match *self {
            Universe(i)                            => write!(f, "Universe {}", i),
            Variable(ref str)                      => write!(f, "{}", str),
            App      (ref left, ref right) => write!(f, "({} {})",            left, right),
            Lambda(ref bound, ref left, ref right) => write!(f, "({}: {}) {}", bound, left, right),
            Forall(ref bound, ref left, ref right) => write!(f, "[{}: {}] {}", bound, left, right),
        }
    }
}
