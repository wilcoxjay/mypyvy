import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.HashMap;
import java.util.Arrays;
import java.util.Iterator;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Expression;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Tuple;
import kodkod.instance.Universe;
public final class _KodkodModel {
enum LeafExprType {
   RELATION,
   FUNCTION,
   CONSTANT,
}
private final Map<String, List<String>> arities;
private final Map<String, Variable> vars;
private final Map<String, Map<Integer, Relation>> relations;
private final Map<String, Map<Integer, Relation>> functions;
private final Map<String, Map<Integer, Relation>> constants;
private final Map<String, Relation> sorts;
public _KodkodModel() {
this.arities = new HashMap<String, List<String>>();
this.vars = new HashMap<String, Variable>();
this.relations = new HashMap<String, Map<Integer, Relation>>();
this.functions = new HashMap<String, Map<Integer, Relation>>();
this.constants = new HashMap<String, Map<Integer, Relation>>();
this.sorts = new HashMap<String, Relation>();
this.sorts.put("__KOD_BOOL__", Relation.unary("__KOD_BOOL__"));
this.sorts.put("node", Relation.unary("node"));
this.sorts.put("quorum", Relation.unary("quorum"));
this.sorts.put("value", Relation.unary("value"));
this.arities.put("member", Arrays.asList("node", "quorum"));
this.arities.put("vote_request_msg", Arrays.asList("node", "node"));
this.arities.put("voted", Arrays.asList("node"));
this.arities.put("vote_msg", Arrays.asList("node", "node"));
this.arities.put("votes", Arrays.asList("node", "node"));
this.arities.put("leader", Arrays.asList("node"));
this.arities.put("decided", Arrays.asList("node", "value"));
this.arities.put("voting_quorum", Arrays.asList("quorum"));
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
// (forall Q1:quorum, Q2:quorum. exists N:node. member(N, Q1) & member(N, Q2)) & ((forall N1:node, N2:node. leader(N1) & leader(N2) -> N1 == N2) & (forall N:node, N1:node. votes(N, N1) -> vote_msg(N1, N)) & (forall N:node, N1:node, N2:node. vote_msg(N, N1) & vote_msg(N, N2) -> N1 == N2) & (forall N:node, N1:node. vote_msg(N, N1) -> voted(N)) & (forall N:node, N1:node. leader(N) & member(N1, voting_quorum) -> votes(N, N1)) & (forall N:node, V:value. decided(N, V) -> leader(N)) & (exists n:node, v:value. (forall V:value, N:node. leader(n) & !decided(n, V) & (new(decided(N, V)) <-> decided(N, V) | N == n & V == v)) & (forall x0:node, x1:node. new(vote_request_msg(x0, x1)) == vote_request_msg(x0, x1)) & (forall x0:node. new(voted(x0)) == voted(x0)) & (forall x0:node, x1:node. new(vote_msg(x0, x1)) == vote_msg(x0, x1)) & (forall x0:node, x1:node. new(votes(x0, x1)) == votes(x0, x1)) & (forall x0:node. new(leader(x0)) == leader(x0)) & new(voting_quorum) == voting_quorum) & new(!(forall N:node, V:value. decided(N, V) -> leader(N))))
return this.get_var("N").product(this.get_var("Q1")).in(this.get_expression("member", LeafExprType.RELATION, 0)).and(this.get_var("N").product(this.get_var("Q2")).in(this.get_expression("member", LeafExprType.RELATION, 0))).forSome(this.get_var("N").oneOf(this.sorts.get("node"))).forAll(this.get_var("Q1").oneOf(this.sorts.get("quorum")).and(this.get_var("Q2").oneOf(this.sorts.get("quorum")))).and(this.get_var("N1").in(this.get_expression("leader", LeafExprType.RELATION, 0)).and(this.get_var("N2").in(this.get_expression("leader", LeafExprType.RELATION, 0))).implies(this.get_var("N1").eq(this.get_var("N2"))).forAll(this.get_var("N1").oneOf(this.sorts.get("node")).and(this.get_var("N2").oneOf(this.sorts.get("node")))).and(this.get_var("N").product(this.get_var("N1")).in(this.get_expression("votes", LeafExprType.RELATION, 0)).implies(this.get_var("N1").product(this.get_var("N")).in(this.get_expression("vote_msg", LeafExprType.RELATION, 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))))).and(this.get_var("N").product(this.get_var("N1")).in(this.get_expression("vote_msg", LeafExprType.RELATION, 0)).and(this.get_var("N").product(this.get_var("N2")).in(this.get_expression("vote_msg", LeafExprType.RELATION, 0))).implies(this.get_var("N1").eq(this.get_var("N2"))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))).and(this.get_var("N2").oneOf(this.sorts.get("node"))))).and(this.get_var("N").product(this.get_var("N1")).in(this.get_expression("vote_msg", LeafExprType.RELATION, 0)).implies(this.get_var("N").in(this.get_expression("voted", LeafExprType.RELATION, 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))))).and(this.get_var("N").in(this.get_expression("leader", LeafExprType.RELATION, 0)).and(this.get_var("N1").product(this.get_expression("voting_quorum", LeafExprType.CONSTANT, 0)).in(this.get_expression("member", LeafExprType.RELATION, 0))).implies(this.get_var("N").product(this.get_var("N1")).in(this.get_expression("votes", LeafExprType.RELATION, 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))))).and(this.get_var("N").product(this.get_var("V")).in(this.get_expression("decided", LeafExprType.RELATION, 0)).implies(this.get_var("N").in(this.get_expression("leader", LeafExprType.RELATION, 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("V").oneOf(this.sorts.get("value"))))).and(this.get_var("n").in(this.get_expression("leader", LeafExprType.RELATION, 0)).and(this.get_var("n").product(this.get_var("V")).in(this.get_expression("decided", LeafExprType.RELATION, 0)).not()).and(this.get_var("N").product(this.get_var("V")).in(this.get_expression("decided", LeafExprType.RELATION, 1)).iff(this.get_var("N").product(this.get_var("V")).in(this.get_expression("decided", LeafExprType.RELATION, 0)).or(this.get_var("N").eq(this.get_var("n")).and(this.get_var("V").eq(this.get_var("v")))))).forAll(this.get_var("V").oneOf(this.sorts.get("value")).and(this.get_var("N").oneOf(this.sorts.get("node")))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("vote_request_msg", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("vote_request_msg", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("node"))))).and(this.get_var("x0").in(this.get_expression("voted", LeafExprType.RELATION, 1)).iff(this.get_var("x0").in(this.get_expression("voted", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("vote_msg", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("vote_msg", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("node"))))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("votes", LeafExprType.RELATION, 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_expression("votes", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("node"))))).and(this.get_var("x0").in(this.get_expression("leader", LeafExprType.RELATION, 1)).iff(this.get_var("x0").in(this.get_expression("leader", LeafExprType.RELATION, 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")))).and(this.get_expression("voting_quorum", LeafExprType.CONSTANT, 1).eq(this.get_expression("voting_quorum", LeafExprType.CONSTANT, 0))).forSome(this.get_var("n").oneOf(this.sorts.get("node")).and(this.get_var("v").oneOf(this.sorts.get("value"))))).and(this.get_var("N").product(this.get_var("V")).in(this.get_expression("decided", LeafExprType.RELATION, 1)).implies(this.get_var("N").in(this.get_expression("leader", LeafExprType.RELATION, 1))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("V").oneOf(this.sorts.get("value")))).not()));
}
public Formula spec() {
   // Function (modeled as kodkod relations) in mypyvy have a total ordering
   List<Formula> functions_spec = new ArrayList<Formula>();
   for(Map<Integer, Relation> m : this.functions.values()) {
      for(Relation f : m.values()) {
         List<String> arity = arities.get(get_relation_name(f));
         if(arity.size() > 0) {
            final List<Relation> domain_sorts = new ArrayList<Relation>();
            for(int i = 0; i < arity.size() - 1; i++) {
               domain_sorts.add(sorts.get(arity.get(i)));
            }
            final Expression domain = Expression.product(domain_sorts);
            functions_spec.add(f.function(domain, this.sorts.get(arity.get(arity.size() - 1))));
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
public Bounds bounds() {
final Universe _univ = new Universe(Arrays.asList("node0", "quorum0", "value0", "__KOD_TRUTH__"));
final TupleFactory _f  = _univ.factory();
final Bounds _b = new Bounds(_univ);
_b.boundExactly(this.sorts.get("node"), _f.range(_f.tuple("node0"), _f.tuple("node0")));
_b.boundExactly(this.sorts.get("quorum"), _f.range(_f.tuple("quorum0"), _f.tuple("quorum0")));
_b.boundExactly(this.sorts.get("value"), _f.range(_f.tuple("value0"), _f.tuple("value0")));
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
   final _KodkodModel model = new _KodkodModel();
   final Solver solver = new Solver();
   solver.options().setSolver(SATFactory.MiniSat);
   final Solution sol = solver.solve(Formula.and(model.formula(), model.spec()), model.bounds());
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
   out += String.format("\n},\n`proof`: `%s`\n}", sol.proof());
   out = out.replace('`', '"');
   System.out.println(out);
}
}