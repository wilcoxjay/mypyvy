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
private final Map<String, Variable> vars;
private final Map<String, Map<Integer, Relation>> relations;
private final Map<String, List<String>> arities;
private final Map<String, Relation> sorts;
public _KodkodModel() {
this.vars = new HashMap<String, Variable>();
this.relations = new HashMap<String, Map<Integer, Relation>>();
this.arities = new HashMap<String, List<String>>();
this.sorts = new HashMap<String, Relation>();
this.sorts.put("node", Relation.unary("node"));
this.sorts.put("quorum", Relation.unary("quorum"));
this.sorts.put("value", Relation.unary("value"));
this.sorts.put("__KOD_BOOL__", Relation.unary("__KOD_BOOL__"));
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
public Relation get_relation(String name, int index) {
   if (!this.relations.containsKey(name)) {
      relations.put(name, new HashMap<Integer, Relation>());
   }
   if (!this.relations.get(name).containsKey(index)) {
       int arity = this.arities.get(name).size() == 0? 1: this.arities.get(name).size();
       this.relations.get(name).put(index, Relation.nary("__" + index + "__" + name, arity));
   }
   return this.relations.get(name).get(index);
}
public String get_relation_name(Relation rel) {
   return rel.name().substring(rel.name().indexOf("__", 2) + 2);
}
public Formula formula() {
// (forall N1:node, N2:node. leader(N1) & leader(N2) -> N1 == N2) & (forall N:node, N1:node. votes(N, N1) -> vote_msg(N1, N)) & (forall N:node, N1:node, N2:node. vote_msg(N, N1) & vote_msg(N, N2) -> N1 == N2) & (forall N:node, N1:node. vote_msg(N, N1) -> voted(N)) & (forall N:node, N1:node. leader(N) & member(N1, voting_quorum) -> votes(N, N1)) & (forall N:node, V:value. decided(N, V) -> leader(N)) & (exists n:node, v:value. (forall V:value, N:node. leader(n) & !decided(n, V) & (new(decided(N, V)) <-> decided(N, V) | N == n & V == v)) & (forall x0:node, x1:node. new(vote_request_msg(x0, x1)) == vote_request_msg(x0, x1)) & (forall x0:node. new(voted(x0)) == voted(x0)) & (forall x0:node, x1:node. new(vote_msg(x0, x1)) == vote_msg(x0, x1)) & (forall x0:node, x1:node. new(votes(x0, x1)) == votes(x0, x1)) & (forall x0:node. new(leader(x0)) == leader(x0)) & new(voting_quorum) == voting_quorum) & new(!(forall N:node, V:value. decided(N, V) -> leader(N)))
return this.get_var("N1").in(this.get_relation("leader", 0)).and(this.get_var("N2").in(this.get_relation("leader", 0))).implies(this.get_var("N1").eq(this.get_var("N2"))).forAll(this.get_var("N1").oneOf(this.sorts.get("node")).and(this.get_var("N2").oneOf(this.sorts.get("node")))).and(this.get_var("N").product(this.get_var("N1")).in(this.get_relation("votes", 0)).implies(this.get_var("N1").product(this.get_var("N")).in(this.get_relation("vote_msg", 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))))).and(this.get_var("N").product(this.get_var("N1")).in(this.get_relation("vote_msg", 0)).and(this.get_var("N").product(this.get_var("N2")).in(this.get_relation("vote_msg", 0))).implies(this.get_var("N1").eq(this.get_var("N2"))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))).and(this.get_var("N2").oneOf(this.sorts.get("node"))))).and(this.get_var("N").product(this.get_var("N1")).in(this.get_relation("vote_msg", 0)).implies(this.get_var("N").in(this.get_relation("voted", 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))))).and(this.get_var("N").in(this.get_relation("leader", 0)).and(this.get_var("N1").product(this.get_relation("voting_quorum", 0)).in(this.get_relation("member", 0))).implies(this.get_var("N").product(this.get_var("N1")).in(this.get_relation("votes", 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("N1").oneOf(this.sorts.get("node"))))).and(this.get_var("N").product(this.get_var("V")).in(this.get_relation("decided", 0)).implies(this.get_var("N").in(this.get_relation("leader", 0))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("V").oneOf(this.sorts.get("value"))))).and(this.get_var("n").in(this.get_relation("leader", 0)).and(this.get_var("n").product(this.get_var("V")).in(this.get_relation("decided", 0)).not()).and(this.get_var("N").product(this.get_var("V")).in(this.get_relation("decided", 1)).iff(this.get_var("N").product(this.get_var("V")).in(this.get_relation("decided", 0)).or(this.get_var("N").eq(this.get_var("n")).and(this.get_var("V").eq(this.get_var("v")))))).forAll(this.get_var("V").oneOf(this.sorts.get("value")).and(this.get_var("N").oneOf(this.sorts.get("node")))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_relation("vote_request_msg", 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_relation("vote_request_msg", 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("node"))))).and(this.get_var("x0").in(this.get_relation("voted", 1)).iff(this.get_var("x0").in(this.get_relation("voted", 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_relation("vote_msg", 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_relation("vote_msg", 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("node"))))).and(this.get_var("x0").product(this.get_var("x1")).in(this.get_relation("votes", 1)).iff(this.get_var("x0").product(this.get_var("x1")).in(this.get_relation("votes", 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")).and(this.get_var("x1").oneOf(this.sorts.get("node"))))).and(this.get_var("x0").in(this.get_relation("leader", 1)).iff(this.get_var("x0").in(this.get_relation("leader", 0))).forAll(this.get_var("x0").oneOf(this.sorts.get("node")))).and(this.get_relation("voting_quorum", 1).eq(this.get_relation("voting_quorum", 0))).forSome(this.get_var("n").oneOf(this.sorts.get("node")).and(this.get_var("v").oneOf(this.sorts.get("value"))))).and(this.get_var("N").product(this.get_var("V")).in(this.get_relation("decided", 1)).implies(this.get_var("N").in(this.get_relation("leader", 1))).forAll(this.get_var("N").oneOf(this.sorts.get("node")).and(this.get_var("V").oneOf(this.sorts.get("value")))).not());
}
public Bounds bounds() {
final Universe _univ = new Universe(Arrays.asList("node0", "node1", "node2", "quorum0", "quorum1", "quorum2", "value0", "value1", "value2", "__KOD_TRUTH__"));
final TupleFactory _f  = _univ.factory();
final Bounds _b = new Bounds(_univ);
_b.boundExactly(this.sorts.get("node"), _f.range(_f.tuple("node0"), _f.tuple("node2")));
_b.boundExactly(this.sorts.get("quorum"), _f.range(_f.tuple("quorum0"), _f.tuple("quorum2")));
_b.boundExactly(this.sorts.get("value"), _f.range(_f.tuple("value0"), _f.tuple("value2")));
_b.boundExactly(this.sorts.get("__KOD_BOOL__"), _f.setOf("__KOD_TRUTH__"));
for(Map<Integer, Relation> m : this.relations.values()) {
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
   final Solution sol = solver.solve(model.formula(), model.bounds());
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