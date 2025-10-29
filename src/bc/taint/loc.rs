use std::collections::HashSet;

use crate::bc::{
    dataflow::ptr::{PointerAnalysis, types::MemLoc},
    types::{Function, Place},
    visit::Visit,
};

pub fn all_memlocs(func: &Function, ptr: &PointerAnalysis) -> HashSet<MemLoc> {
    all_places(func)
        .into_iter()
        .flat_map(|place| ptr.could_refer_to(&place))
        .collect()
}

fn all_places(func: &Function) -> HashSet<Place> {
    let mut pv = PlaceVisitor(HashSet::new());
    pv.visit_function(func);
    pv.0
}

struct PlaceVisitor(HashSet<Place>);

impl Visit for PlaceVisitor {
    fn visit_rvalue_place(&mut self, place: &Place, _loc: crate::bc::types::Location) {
        self.0.insert(*place);
    }

    fn visit_lvalue(&mut self, place: &Place, _loc: crate::bc::types::Location) {
        self.0.insert(*place);
    }
}
