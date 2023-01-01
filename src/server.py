# an experimental mypyvy server. could be useful in the future for better distributed computing
#
# run the server:
#
#     python3 -m flask --app src/server --debug run -p 5000
#
# then navigate to
#
#     http://localhost:5000/verify?filename=examples%2Flockserv.pyv
#
# in your browser
#
#
# for more complex queries, send a json object via POST, for example, using curl from the command line:
#     curl -i -H 'Content-Type: application/json' -X POST \
#         -d "{\"filename\": \"examples/lockserv.pyv\", \"options\": [\"--timeout=2000\"]}" \
#         http://localhost:5000/verify

# type: ignore

import logic
import mypyvy
import syntax
import utils

import flask
from typing import Any, Dict, List, Optional

app = flask.Flask('mypyvy')

def get_args() -> Dict[Any, Any]:
    req: Dict[Any, Any] = {}
    if flask.request.method == "POST":
        x = flask.request.get_json()
        if not isinstance(x, dict):
            flask.abort(400, 'request must be json object')
        req = x

    req.update(flask.request.args)

    return req

def parse_program_from_request(verb: str) -> Optional[syntax.Program]:
    req = get_args()

    filename = req.get('filename')
    if filename is None:
        flask.abort(400, 'filename required')

    options: List[str] = req.get('options', [])
    mypyvy.parse_args([verb, filename] + options)
    return mypyvy.parse_file(filename)

@app.route("/typecheck", methods=["GET", "POST"])
def typecheck() -> Any:
    prog = parse_program_from_request('typecheck')

    if prog is None:
        return flask.jsonify(success=False, reason="Parse error")

    success = mypyvy.typecheck_program(prog)
    if not success:
        return flask.jsonify(success=False, reason="Typechecking error")

    return flask.jsonify(success=True)

@app.route("/verify", methods=["GET", "POST"])
def verify() -> Any:
    prog = parse_program_from_request('verify')

    if prog is None:
        return flask.jsonify(success=False, reason="Parse error")

    success = mypyvy.typecheck_program(prog)
    if not success:
        return flask.jsonify(success=False, reason="Typechecking error")

    syntax.the_program = prog

    s = logic.Solver(use_cvc4=utils.args.cvc4)

    try:
        success = mypyvy.verify(s)
    except logic.SolverReturnedUnknown:
        return flask.jsonify(success=False, reason="Verification returned unknown")

    if not success:
        return flask.jsonify(success=False, reason="Verification error")

    return flask.jsonify(success=True)
