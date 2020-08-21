import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.util.Arrays;
import java.util.Iterator;
import java.util.Collection;;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Expression;
import kodkod.ast.Variable;
import kodkod.ast.Decls;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Tuple;
import kodkod.instance.Universe;
public final class _KOD_paxos_forall {
enum LeafExprType {
   RELATION,
   FUNCTION,
   CONSTANT,
};
private final Map<String, List<String>> arities;
private final Map<String, Variable> vars;
private final Map<String, Map<Integer, Relation>> relations;
private final Map<String, Map<Integer, Relation>> functions;
private final Map<String, Map<Integer, Relation>> constants;
private final Map<String, Relation> sorts;
public _KOD_paxos_forall() {
this.arities = new HashMap<String, List<String>>();
this.vars = new HashMap<String, Variable>();
this.relations = new HashMap<String, Map<Integer, Relation>>();
this.functions = new HashMap<String, Map<Integer, Relation>>();
this.constants = new HashMap<String, Map<Integer, Relation>>();
this.sorts = new HashMap<String, Relation>();
this.sorts.put("__KOD_BOOL__", Relation.unary("__KOD_BOOL__"));
this.sorts.put("node", Relation.unary("node"));
this.sorts.put("value", Relation.unary("value"));
this.sorts.put("quorum", Relation.unary("quorum"));
this.sorts.put("round", Relation.unary("round"));
this.arities.put("le", Arrays.asList("round", "round"));
this.arities.put("member", Arrays.asList("node", "quorum"));
this.arities.put("one_a", Arrays.asList("round"));
this.arities.put("one_b", Arrays.asList("node", "round"));
this.arities.put("left_round", Arrays.asList("node", "round"));
this.arities.put("proposal", Arrays.asList("round", "value"));
this.arities.put("vote", Arrays.asList("node", "round", "value"));
this.arities.put("decision", Arrays.asList("round", "value"));
this.arities.put("decision_quorum", Arrays.asList("round", "value", "quorum"));
this.arities.put("choosable_node", Arrays.asList("round", "value", "quorum", "node"));
this.arities.put("none", Arrays.asList("round"));
}

public Variable get_var(String name) {
  if(!this.vars.containsKey(name)) {
    vars.put(name, Variable.unary(name));
  }
  return this.vars.get(name);
}
public Relation get_expression(String name, LeafExprType t, int index) {
   final Map<String, Map<Integer, Relation>> m;
   switch(t)
   {
      case RELATION: m = this.relations; break;
      case FUNCTION: m = this.functions; break;
      case CONSTANT: m = this.constants; break;
      default: m = this.constants;; // TODO: Raise Exception
   }
   if (!m.containsKey(name)) {
      m.put(name, new HashMap<Integer, Relation>());
   }
   if (!m.get(name).containsKey(index)) {
      int arity = this.arities.get(name).size() == 0? 1: this.arities.get(name).size();
      m.get(name).put(index, Relation.nary("__" + index + "__" + name, arity));
   }
   return m.get(name).get(index);
}
public String get_relation_name(Relation rel) {
   return rel.name().substring(rel.name().indexOf("__", 2) + 2);
}
public Formula formula() {
// (forall X:round. le(X, X)) & (forall X:round, Y:round, Z:round. le(X, Y) & le(Y, Z) -> le(X, Z)) & (forall X:round, Y:round. le(X, Y) & le(Y, X) -> X == Y) & (forall X:round, Y:round. le(X, Y) | le(Y, X)) & (forall Q1:quorum, Q2:quorum. exists N:node. member(N, Q1) & member(N, Q2)) & ((forall R:round, V1:value, V2:value. proposal(R, V1) & proposal(R, V2) -> V1 == V2) & (forall N:node, R:round, V:value. vote(N, R, V) -> proposal(R, V)) & (forall R:round, V:value, N:node, Q:quorum. decision(R, V) & member(N, Q) & Q == decision_quorum(R, V) -> vote(N, R, V)) & (forall N:node, V:value. !vote(N, none, V)) & (forall N:node, R2:round, R1:round. one_b(N, R2) & !le(R2, R1) -> left_round(N, R1)) & (forall N1:node, Q:quorum, R:round, V:value, N2:node. member(N1, Q) & left_round(N1, R) & !vote(N1, R, V) & N2 == choosable_node(R, V, Q) -> member(N2, Q) & left_round(N2, R) & !vote(N2, R, V)) & (forall N:node. forall R1:round, R2:round, V1:value, V2:value, Q:quorum. !le(R2, R1) & proposal(R2, V2) & V1 != V2 & N == choosable_node(R1, V1, Q) -> member(N, Q) & left_round(N, R1) & !vote(N, R1, V1)) & (exists r:round. r != none & (forall R:round. new(one_a(R)) <-> one_a(R) | R == r) & (forall x0:node, x1:round. new(one_b(x0, x1)) == one_b(x0, x1)) & (forall x0:node, x1:round. new(left_round(x0, x1)) == left_round(x0, x1)) & (forall x0:round, x1:value. new(proposal(x0, x1)) == proposal(x0, x1)) & (forall x0:node, x1:round, x2:value. new(vote(x0, x1, x2)) == vote(x0, x1, x2)) & (forall x0:round, x1:value. new(decision(x0, x1)) == decision(x0, x1)) & (forall x0:round, x1:value. new(decision_quorum(x0, x1)) == decision_quorum(x0, x1)) & (forall x0:round, x1:value, x2:quorum. new(choosable_node(x0, x1, x2)) == choosable_node(x0, x1, x2))) & new(!(forall R:round, V1:value, V2:value. proposal(R, V1) & proposal(R, V2) -> V1 == V2)))
return this.get_var("X").product(this.get_var("X")).in(this.get_expression("le", LeafExprType.RELATION, 0)).forAll(this.get_var("X").oneOf(this.sorts.get("round"))).and(this.get_var("X").product(this.get_var("Y")).in(this.get_expression("le", LeafExprType.RELATION, 0)).and(this.get_var("Y").product(this.get_var("Z")).in(this.get_expression("le", LeafExprType.RELATION, 0))).implies(this.get_var("X").product(this.get_var("Z")).in(this.get_expression("le", LeafExprType.RELATION, 0))).forAll(this.get_var("X").oneOf(this.sorts.get("round")).and(this.get_var("Y").oneOf(this.sorts.get("round"))).and(this.get_var("Z").oneOf(this.sorts.get("round"))))).and(this.get_var("X").product(this.get_var("Y")).in(this.get_expression("le", LeafExprType.RELATION, 0)).and(this.get_var("Y").product(this.get_var("X")).in(this.get_expression("le", LeafExprType.RELATION, 0))).implies(this.get_var("X").eq(this.get_var("Y"))).forAll(this.get_var("X").oneOf(this.sorts.get("round")).and(this.get_var("Y").oneOf(this.sorts.get("round"))))).and(this.get_var("X").product(this.get_var("Y")).in(this.get_expression("le", LeafExprType.RELATION, 0)).or(this.get_var("Y").product(this.get_var("X")).in(this.get_expression("le", LeafExprType.RELATION, 0))).forAll(this.get_var("X").oneOf(this.sorts.get("round")).and(this.get_var("Y").oneOf(this.sorts.get("round"))))).and(this.get_var("N").product(this.get_var("Q1")).in(this.get_expression("member", LeafExprType.RELATION, 0)).and(this.get_var("N").product(this.get_var("Q2")).in(this.get_expression("member", LeafExprType.RELATION, 0))).forSome(this.get_var("N").oneOf(this.sorts.get("node"))).forAll(this.get_var("Q1").oneOf(this.sorts.get("quorum")).and(this.get_var("Q2").oneOf(this.sorts.get("quorum"))))).and(this.get_var("R").product(this.get_var("V1")).in(this.get_expression("proposal", LeafExprType.RELATION, 0)).and(this.get_var("R").product(this.get_var("V2")).in(this.get_expression("proposal", LeafExprType.RELATION, 0))).implies(this.get_var("V1").eq(this.get_var("V2"))).forAll(this.get_var("R").oneOf(this.sorts.get("round")).and(this.get_var("V1").oneOf(this.sorts.get("value"))).and(this.get_var("V2").oneOf(this.sorts.get("value")))).and(this.get_var("N").product(this.get_var("R")).product(this.get_var("V")).in(this.get_expression("vote", LeafExprType.RELATION, 0)).implies(this.get_var("R").product(this.get_var("V")).in(this.get_expression("proposal", LeafExprType.RELATION, 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("R").oneOf(this.sorts.get("round"))).and(this.get_var("V").oneOf(this.sorts.get("value"))))).and(this.get_var("R").product(this.get_var("V")).in(this.get_expression("decision", LeafExprType.RELATION, 0)).and(this.get_var("N").product(this.get_var("Q")).in(this.get_expression("member", LeafExprType.RELATION, 0))).and(this.get_var("Q").eq(this.get_var("R").join(this.get_var("V").join(this.get_expression("decision_quorum", LeafExprType.FUNCTION, 0))))).implies(this.get_var("N").product(this.get_var("R")).product(this.get_var("V")).in(this.get_expression("vote", LeafExprType.RELATION, 0))).forAll(this.get_var("R").oneOf(this.sorts.get("round")).and(this.get_var("V").oneOf(this.sorts.get("value"))).and(this.get_var("N").oneOf(this.sorts.get("node"))).and(this.get_var("Q").oneOf(this.sorts.get("quorum"))))).and(this.get_var("N").product(this.get_expression("none", LeafExprType.CONSTANT, 0)).product(this.get_var("V")).in(this.get_expression("vote", LeafExprType.RELATION, 0)).not().forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("V").oneOf(this.sorts.get("value"))))).and(this.get_var("N").product(this.get_var("R2")).in(this.get_expression("one_b", LeafExprType.RELATION, 0)).and(this.get_var("R2").product(this.get_var("R1")).in(this.get_expression("le", LeafExprType.RELATION, 0)).not()).implies(this.get_var("N").product(this.get_var("R1")).in(this.get_expression("left_round", LeafExprType.RELATION, 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("R2").oneOf(this.sorts.get("round"))).and(this.get_var("R1").oneOf(this.sorts.get("round"))))).and(this.get_var("N1").product(this.get_var("Q")).in(this.get_expression("member", LeafExprType.RELATION, 0)).and(this.get_var("N1").product(this.get_var("R")).in(this.get_expression("left_round", LeafExprType.RELATION, 0))).and(this.get_var("N1").product(this.get_var("R")).product(this.get_var("V")).in(this.get_expression("vote", LeafExprType.RELATION, 0)).not()).and(this.get_var("N2").eq(this.get_var("R").join(this.get_var("V").join(this.get_var("Q").join(this.get_expression("choosable_node", LeafExprType.FUNCTION, 0)))))).implies(this.get_var("N2").product(this.get_var("Q")).in(this.get_expression("member", LeafExprType.RELATION, 0)).and(this.get_var("N2").product(this.get_var("R")).in(this.get_expression("left_round", LeafExprType.RELATION, 0))).and(this.get_var("N2").product(this.get_var("R")).product(this.get_var("V")).in(this.get_expression("vote", LeafExprType.RELATION, 0)).not())).forAll(this.get_var("N1").oneOf(this.sorts.get("node")).and(this.get_var("Q").oneOf(this.sorts.get("quorum"))).and(this.get_var("R").oneOf(this.sorts.get("round"))).and(this.get_var("V").oneOf(this.sorts.get("value"))).and(this.get_var("N2").oneOf(this.sorts.get("node"))))).and(this.get_var("R2").product(this.get_var("R1")).in(this.get_expression("le", LeafExprType.RELATION, 0)).not().and(this.get_var("R2").product(this.get_var("V2")).in(this.get_expression("proposal", LeafExprType.RELATION, 0))).and(this.get_var("V1").eq(this.get_var("V2")).not()).and(this.get_var("N").eq(this.get_var("R1").join(this.get_var("V1").join(this.get_var("Q").join(this.get_expression("choosable_node", LeafExprType.FUNCTION, 0)))))).implies(this.get_var("N").product(this.get_var("Q")).in(this.get_expression("member", LeafExprType.RELATION, 0)).and(this.get_var("N").product(this.get_var("R1")).in(this.get_expression("left_round", LeafExprType.RELATION, 0))).and(this.get_var("N").product(this.get_var("R1")).product(this.get_var("V1")).in(this.get_expression("vote", LeafExprType.RELATION, 0)).not())).forAll(this.get_var("R1").oneOf(this.sorts.get("round")).and(this.get_var("R2").oneOf(this.sorts.get("round"))).and(this.get_var("V1").oneOf(this.sorts.get("value"))).and(this.get_var("V2").oneOf(this.sorts.get("value"))).and(this.get_var("Q").oneOf(this.sorts.get("quorum")))).forAll(this.get_var("N").oneOf(this.sorts.get("node")))).and(this.get_var("r").eq(this.get_expression("none", LeafExprType.CONSTANT, 0)).not().and(this.get_var("R").in(this.get_expression("one_a", LeafExprType.RELATION, 1)).iff(this.get_var("R").in(this.get_expression("one_a", LeafExprType.RELATION, 0)).or(this.get_var("R").eq(this.get_var("r")))).forAll(this.get_var("R").oneOf(this.sorts.get("round")))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("one_b", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("one_b", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("round"))))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("left_round", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("left_round", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("round"))))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("proposal", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("proposal", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("round")).and(this.get_var("x1").oneOf(this.sorts.get("value"))))).and(this.get_var("x0").product(this.get_var("x1")).product(this.get_var("x2")).in(this.get_expression("vote", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).product(this.get_var("x2")).in(this.get_expression("vote", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("round"))).and(this.get_var("x2").oneOf(this.sorts.get("value"))))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("decision", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("decision", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("round")).and(this.get_var("x1").oneOf(this.sorts.get("value"))))).and(this.get_var("x0").join(this.get_var("x1").join(this.get_expression("decision_quorum", LeafExprType.FUNCTION, 1))).eq(this.get_var("x0").join(this.get_var("x1").join(this.get_expression("decision_quorum", LeafExprType.FUNCTION, 0)))).forAll(this.get_var("x0").oneOf(this.sorts.get("round")).and(this.get_var("x1").oneOf(this.sorts.get("value"))))).and(this.get_var("x0").join(this.get_var("x1").join(this.get_var("x2").join(this.get_expression("choosable_node", LeafExprType.FUNCTION, 1)))).eq(this.get_var("x0").join(this.get_var("x1").join(this.get_var("x2").join(this.get_expression("choosable_node", LeafExprType.FUNCTION, 0))))).forAll(this.get_var("x0").oneOf(this.sorts.get("round")).and(this.get_var("x1").oneOf(this.sorts.get("value"))).and(this.get_var("x2").oneOf(this.sorts.get("quorum"))))).forSome(this.get_var("r").oneOf(this.sorts.get("round")))).and(this.get_var("R").product(this.get_var("V1")).in(this.get_expression("proposal", LeafExprType.RELATION, 1)).and(this.get_var("R").product(this.get_var("V2")).in(this.get_expression("proposal", LeafExprType.RELATION, 1))).implies(this.get_var("V1").eq(this.get_var("V2"))).forAll(this.get_var("R").oneOf(this.sorts.get("round")).and(this.get_var("V1").oneOf(this.sorts.get("value"))).and(this.get_var("V2").oneOf(this.sorts.get("value")))).not()));
}
public Formula spec() {
   // Function (modeled as kodkod relations) in mypyvy have a total ordering
   List<Formula> functions_spec = new ArrayList<Formula>();
   for(Map<Integer, Relation> m : this.functions.values()) {
      for(Relation f : m.values()) {
         Expression joined = f;
         // Last sort is sort of range
         List<String> function_arguments = arities.get(get_relation_name(f))
                                             .subList(0, arities.get(get_relation_name(f)).size() - 1);
         if(function_arguments.size() > 0){
            joined = get_var("X0").join(joined);
            Decls dcls = get_var("X0").oneOf(sorts.get(function_arguments.get(0)));
            for(int ind = 1; ind < function_arguments.size(); ind++) {
               joined = get_var("X" + ind).join(joined);
               dcls = dcls.and(get_var("X" + ind).oneOf(sorts.get(function_arguments.get(ind))));
            }
            functions_spec.add(joined.one().forAll(dcls));
         }
      }
   }
   final Formula functions_totality = Formula.and(functions_spec);
   // Constants (modeled as kodkod relations) must contain exactly one value
   List<Formula> constants_spec = new ArrayList<Formula>();
   for(Map<Integer, Relation> m : constants.values()) {
       for(Relation r : m.values()) {
            constants_spec.add(r.one());
       }
   }
   final Formula constants_singularity = Formula.and(constants_spec);
   return Formula.and(functions_totality, constants_singularity);
}
public Bounds bounds(int _bounds) {
   List<String> atoms = new ArrayList<>(((sorts.size() - 1) * _bounds) + 1); // -1 for __KOD_BOOL__
   for(Relation sort: sorts.values()) {
      for(int i = 0; i < _bounds; i++) {
         atoms.add(sort.name() + i);
      }
   }
   atoms.add("__KOD_TRUTH__");
   final Universe _univ = new Universe(atoms);
   final TupleFactory _f  = _univ.factory();
   final Bounds _b = new Bounds(_univ);
_b.boundExactly(this.sorts.get("node"), _f.range(_f.tuple("node0"), _f.tuple("node" + (_bounds - 1))));
_b.boundExactly(this.sorts.get("value"), _f.range(_f.tuple("value0"), _f.tuple("value" + (_bounds - 1))));
_b.boundExactly(this.sorts.get("quorum"), _f.range(_f.tuple("quorum0"), _f.tuple("quorum" + (_bounds - 1))));
_b.boundExactly(this.sorts.get("round"), _f.range(_f.tuple("round0"), _f.tuple("round" + (_bounds - 1))));
_b.boundExactly(this.sorts.get("__KOD_BOOL__"), _f.setOf("__KOD_TRUTH__"));
final Map<String, Map<Integer, Relation>> mapOfExprs = new HashMap<>(this.relations);
mapOfExprs.putAll(this.functions);
mapOfExprs.putAll(this.constants);
for(Map<Integer, Relation> m : mapOfExprs.values()) {
   for(Relation rel: m.values()){
      Iterator<String> it = this.arities.get(this.get_relation_name(rel)).iterator();
      if(it.hasNext()) {
         TupleSet up_bounds = _b.upperBound(this.sorts.get(it.next())); 
         while(it.hasNext()) {
            up_bounds = up_bounds.product(_b.upperBound(this.sorts.get(it.next())));
         }
         _b.bound(rel, up_bounds);
      }
   }
}
return _b;
}

public static void main(String[] args) {
   final _KOD_paxos_forall model = new _KOD_paxos_forall();
   final Solver solver = new Solver();
   solver.options().setSolver(SATFactory.MiniSat);
   final Solution sol = solver.solve(Formula.and(model.formula(), model.spec()), model.bounds(3));
   String out = String.format("{\n`outcome`: `%s`,\n`instance`:{\n", sol.outcome());
   if (sol.sat()) {
      for (Map.Entry<Relation, TupleSet> me : sol.instance().relationTuples().entrySet()) {
         out += String.format("`%s`: [", me.getKey());
         Iterator<Tuple> it = me.getValue().iterator();
         while (it.hasNext()) {
            out += "[";
            Tuple t = it.next();
            for (int i = 0; i < t.arity(); i++) {
            out += String.format("`%s`, ", t.atom(i));
         }
         out += "],";
         }
      out += "],\n";
      }
   }
   out += String.format("\n},\n`proof`: `%s`,\n`translation_time`: %s, `solving_time`: %s,\n}", sol.proof(), sol.stats().translationTime(), sol.stats().solvingTime());
   out = out.replace('`', '"');
   System.out.println(out);
}
}