import java.util.ArrayList;
import java.util.List;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
public final class _kodkod_model {
private final Relation client;
private final Relation server;
private final Relation id;
private final Relation used;
private final Relation new_used;
private final Relation server_holds_lock;
private final Relation new_server_holds_lock;
private final Relation holds_lock;
private final Relation new_holds_lock;
private final Relation request_msg;
private final Relation new_request_msg;
private final Relation grant_msg;
private final Relation new_grant_msg;
private final Relation release_msg;
private final Relation new_release_msg;
public _kodkod_model() {
this.client = Relation.nary("client", 1);
this.server = Relation.nary("server", 1);
this.id = Relation.nary("id", 1);
this.used = Relation.nary("used", 1);
this.new_used = Relation.nary("new_used", 1);
this.server_holds_lock = Relation.nary("server_holds_lock", 1);
this.new_server_holds_lock = Relation.nary("new_server_holds_lock", 1);
this.holds_lock = Relation.nary("holds_lock", 2);
this.new_holds_lock = Relation.nary("new_holds_lock", 2);
this.request_msg = Relation.nary("request_msg", 3);
this.new_request_msg = Relation.nary("new_request_msg", 3);
this.grant_msg = Relation.nary("grant_msg", 3);
this.new_grant_msg = Relation.nary("new_grant_msg", 3);
this.release_msg = Relation.nary("release_msg", 3);
this.new_release_msg = Relation.nary("new_release_msg", 3);
}

public Formula inits() {
final Variable c1 = Variable.unary("c1");
final Variable c2 = Variable.unary("c2");
final Variable s1 = Variable.unary("s1");
final Variable s2 = Variable.unary("s2");
final Variable i1 = Variable.unary("i1");
final Variable i2 = Variable.unary("i2");
final List<Formula> inits = new ArrayList<Formula>();
inits.add(s.in(server_holds_lock).forAll(s.oneOf(Server)));
inits.add(used.no());
inits.add(holds_lock.no());
inits.add(request_msg.no());
inits.add(grant_msg.no());
inits.add(release_msg.no());
return Formula.and(inits);
}

public Bounds bounds(int client, int server, int id) {
final List<String> atoms = new ArrayList<String>(_b0 + _b1 + _b2);
}

public void checkInits(int _b0, int _b1, int _b2) {
final Solver solver = new Solver();
solver.options().setSolver(SATFactory.MiniSat);
final Solution sol = solver.solve(this.inits(), get_bounds(_b0, _b1, _b2));
System.out.println(sol);
}

public void checkTransitions(int _b0, int _b1, int _b2) {
final Solver solver = new Solver();
solver.options().setSolver(SATFactory.MiniSat);
}

public static void main(String[] args) {
final _kodkod_model model = new _kodkod_model();
final int _b0 = Integer.parseInt(args[0]);
final int _b1 = Integer.parseInt(args[1]);
final int _b2 = Integer.parseInt(args[2]);
model.checkInits(_b0, _b1, _b2);
model.checkTransitions(_b0, _b1, _b2);
}
}