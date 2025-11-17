use rustc_middle::traits::solve::Goal;
use rustc_middle::ty;
use rustc_trait_selection::solve::inspect::{
    InspectCandidate, InspectGoal, ProbeKind, ProofTreeVisitor,
};

pub(super) struct DumpTree {
    depth: usize,
}

impl DumpTree {
    pub(super) fn new() -> Self {
        Self { depth: 0 }
    }
}

impl<'tcx> ProofTreeVisitor<'tcx> for DumpTree {
    fn span(&self) -> rustc_span::Span {
        rustc_span::DUMMY_SP
    }

    fn visit_goal(&mut self, goal: &InspectGoal<'_, 'tcx>) {
        print_goal(goal, self.depth);

        self.depth += 1;
        for (index, candidate) in goal.candidates().into_iter().enumerate() {
            print_candidate(&candidate, index, self.depth);

            self.depth += 1;
            candidate.visit_nested_in_probe(self);
            self.depth -= 1;
        }
        self.depth -= 1;
    }
}

fn print_goal(goal: &InspectGoal<'_, '_>, depth: usize) {
    let prefix = " ".repeat(depth);

    eprintln!(
        "[[next]]  {prefix}(G) {:?}  {:?}  #C={}  {}",
        goal.result(),
        goal.source(),
        goal.candidates().len(),
        stringify_goal(goal.goal()),
    );
}

fn stringify_goal(goal: Goal<'_, ty::Predicate<'_>>) -> String {
    // NOTE: We omit the ParamEnv … for now

    let kind = goal.predicate.kind();

    format!("for{:?} {:?}", kind.bound_vars(), kind.skip_binder())
}

fn print_candidate(candidate: &InspectCandidate<'_, '_>, index: usize, depth: usize) {
    let prefix = " ".repeat(depth);

    eprintln!(
        "[[next]]  {prefix}(C#{index}) {:?}  {}",
        candidate.result(),
        match candidate.kind() {
            ProbeKind::TraitCandidate { source, result: _ } => format!("TraitCandidate/{source:?}"),
            kind => format!("{kind:?}"),
        },
    );
}
