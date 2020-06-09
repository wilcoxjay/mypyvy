
import subprocess, os, signal, sys, json, threading, time, argparse, random, os.path
from concurrent.futures import ThreadPoolExecutor
from typing import *

class ResultsLogger(object):
    def __init__(self, fn: str):
        self.lock = threading.Lock()
        self.data: List[Any] = []
        self.last_written: float = 0
        self.filename = fn
    def add_result(self, result: Any) -> None:
        with self.lock:
            self.data.append(result)
            if time.time() > self.last_written + 30:
                self._write()
    def _write(self) -> None:
        with open(self.filename, "w") as f:
            json.dump(self.data, f, indent=1)
        self.last_written = time.time()
    def close(self) -> None:
        with self.lock:
            self._write()


def run(r: Any, logger: ResultsLogger) -> None:
    start = time.monotonic()
    try:
        outfile = open(r['log'], "w")
        proc = subprocess.Popen(r['args'], stdout = outfile, stderr=subprocess.STDOUT,
                                encoding = 'utf-8', start_new_session=True)
        
        ret = proc.wait(timeout = r['timeout'])
        if ret == 0:
            r['success'] = True
        else:
            r['success'] = False
        r['killed'] = False
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(proc.pid), signal.SIGTERM) 
        r['killed'] = True
        r['success'] = False
    except Exception as e:
        print(e)
    r['elapsed'] = time.monotonic() - start
    logger.add_result(r)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", "-o", metavar="OUT", required=True, help="output file to write")
    parser.add_argument("--timeout", metavar='T', type=float, default = 10*60, help="timeout for inference")
    parser.add_argument("--count", metavar='N', type=int, default = 1, help="number of times run each example")
    parser.add_argument("--cpus", type=int, default=os.cpu_count(), help="number of concurrent processes to run")
    parser.add_argument("--log-dir", metavar="D", required=True, help="where to write output logs (must be existing directory)")
    parser.add_argument("--single", metavar="E", required=False, help="only run this example")
    parser.add_argument("args", nargs=argparse.REMAINDER, help="arguments to fol-ic3")
    
    args = parser.parse_args()
    
    
    logger = ResultsLogger(args.output)
    extra_args =  args.args if len(args.args) == 0 or args.args[0] != '--' else args.args[1:]
    descs = [
        ("bosco_3t_safety", False),
        ("client_server_ae", False),
        ("client_server_db_ae", False),
        ("consensus_epr", False),
        ("consensus_forall", True),
        ("consensus_wo_decide", True),
        ("firewall", False),
        ("hybrid_reliable_broadcast_cisa", False),
        ("learning_switch", True),
        ("lockserv", True),
        ("paxos_epr", False),
        ("raft", False),
        ("ring_id_not_dead", False),
        ("ring_id", True),
        ("sharded_kv_no_lost_keys", False),
        ("sharded_kv", True),
        ("ticket", True),
        ("toy_consensus_epr", False),
        ("toy_consensus_forall", True)]

    with ThreadPoolExecutor(max_workers=args.cpus) as executor:
        for i in range(args.count):
            random.shuffle(descs)
            for (name, is_universal) in descs:
                if args.single and name != args.single:
                    continue
                a = (['--logic=universal'] if is_universal else []) + (['--cvc4'] if not is_universal else []) + extra_args + [f'examples/fol/{name}.pyv']
                r = {"name": name,
                     "index": i,
                     "timeout": args.timeout,
                     "log": os.path.join(args.log_dir, f"log_{name}_{i}.out"),
                     "args": ['python3', 'src/mypyvy.py', 'fol-ic3'] + a}
            
                executor.submit(run, r, logger)
    logger.close()

if __name__ == '__main__':
    main()
