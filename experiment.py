
import subprocess, os, signal, sys, json, threading, time, argparse, random, traceback
from os import path
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
        print(traceback.format_exc())
    r['elapsed'] = time.monotonic() - start
    logger.add_result(r)

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", "-o", metavar="OUT", required=True, help="output file to write")
    parser.add_argument("--timeout", metavar='T', type=float, default = 60*60, help="timeout for inference")
    parser.add_argument("--count", metavar='N', type=int, default = 1, help="number of times run each example")
    parser.add_argument("--cpus", type=int, default=os.cpu_count(), help="number of concurrent processes to run")
    parser.add_argument("--log-dir", metavar="D", required=True, help="where to write output logs (must be existing directory)")
    parser.add_argument("--single", metavar="E", required=False, help="only run this example")
    parser.add_argument("args", nargs=argparse.REMAINDER, help="arguments to fol-ic3")
    
    args = parser.parse_args()
    
    os.makedirs(path.abspath(args.log_dir), exist_ok=True)
    logger = ResultsLogger(args.output)
    extra_args =  args.args if len(args.args) == 0 or args.args[0] != '--' else args.args[1:]
    common_name = path.splitext(path.basename(args.output))[0]
    
    def make_ic3_cmd(base, is_universal):
        cmd = ['fol-ic3']
        if is_universal:
            cmd.append('--logic=universal')
        else:
            cmd.append('--cvc4')
        cmd.extend(extra_args)
        cmd.append(f'examples/fol/{name}.pyv')
        return cmd

    def make_updr_cmd(base, is_universal):
        assert is_universal
        return ['updr', '--log=info', f'examples/fol/{name}.pyv']
    
            # Existentials:
    descs = [('client_server_ae', False),
            ('client_server_db_ae', False),
            ('consensus_epr', False),
            ('firewall', False),
            ('hybrid_reliable_broadcast_cisa', False),
            ('ring_id_not_dead', False),
            ('sharded_kv_no_lost_keys', False),
            ('toy_consensus_epr', False),

            # Universal only:
            ('consensus_forall', True),
            ('consensus_wo_decide', True),
            ('learning_switch', True),
            ('lockserv', True),
            ('ring_id', True),
            ('sharded_kv', True),
            ('ticket', True),
            ('toy_consensus_forall', True)]


    with ThreadPoolExecutor(max_workers=args.cpus) as executor:
        for i in range(args.count):
            random.shuffle(descs)
            for (name, is_universal) in descs:
                if args.single and name != args.single:
                    continue
                a = make_ic3_cmd(name, is_universal)
                r = {"name": name,
                     "index": i,
                     "type": "fol-ic3",
                     "timeout": args.timeout,
                     "log": path.join(args.log_dir, f"{common_name}-log-fol-ic3-{name}-{i}.out"),
                     "args": ['python3.7', '-u', 'src/mypyvy.py'] + a}
                executor.submit(run, r, logger)

                if is_universal:
                    a = make_updr_cmd(name, is_universal)
                    r = {"name": name,
                        "index": i,
                        "type": "updr",
                        "timeout": args.timeout,
                        "log": path.join(args.log_dir, f"{common_name}-log-updr-{name}-{i}.out"),
                        "args": ['python3.7', '-u', 'src/mypyvy.py'] + a}
                    executor.submit(run, r, logger)

                
    logger.close()

if __name__ == '__main__':
    main()
