import argparse
import collections
import concurrent.futures
import dataclasses
from dataclasses import dataclass
from datetime import datetime
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import threading

from typing import cast, Dict, IO, List, Optional

# This class is actually unused at runtime. We just use it to statically check for typos in accessing options.
class NightlyArgs:
    output_directory: str
    job_timeout: int
    job_suffix: Optional[str]
    num_threads: int
    mypyvy_path: Path
    no_run: bool
    no_analyze: bool
    no_publish: bool
    num_seeds: int

args: NightlyArgs = cast(NightlyArgs, None)

def parse_args() -> None:
    global args

    argparser = argparse.ArgumentParser()
    argparser.add_argument('output_directory', nargs='?',
                           help='name of directory where output is stored')
    argparser.add_argument('--job-suffix',
                           help='string to append (with dash) to the generated output directory name')
    argparser.add_argument('--job-timeout', default='60', type=int,
                           help='number of seconds to allow each job to run before killing it')
    argparser.add_argument('-j', '--num-threads', type=int,
                           help='number of threads to run in parallel (default: n_cpu - 1)')
    argparser.add_argument('--mypyvy-path', type=Path,
                           help='path to mypyvy repository (default: /path/to/nightly.py/../..)')
    argparser.add_argument('--no-run', action='store_true',
                           help='do not run jobs, just analyze and/or publish results in existing directory')
    argparser.add_argument('--no-analyze', action='store_true',
                           help='do not analyze the results')
    argparser.add_argument('--no-publish', action='store_true',
                           help='do not copy the results to the published directory')
    argparser.add_argument('--num-seeds', type=int, default='1',
                           help='how many different random seeds to run for each job')

    args = cast(NightlyArgs, argparser.parse_args(sys.argv[1:]))

    if args.no_run and args.output_directory is None:
        print('--no-run requires output_directory to be passed')
        argparser.print_help()
        sys.exit(1)

    if args.no_run and args.no_analyze:
        print('passing --no-run and --no-analyze means there is nothing to do. exiting.')
        sys.exit(0)

    if args.mypyvy_path is None:
        args.mypyvy_path = Path(__file__).parent.parent

@dataclass
class Job:
    example_name: str
    key: Optional[str]
    mypyvy_cmdline_args: List[str]

def format_datetime(d: datetime) -> str:
    return d.strftime('%Y%m%d-%H%M%S')

JOB_LOG_DIR = 'job-logs'

class JobRunner:
    def __init__(self, output_dir_name: Optional[str] = None) -> None:
        self.start_time = datetime.now()
        if output_dir_name is None:
            output_dir_name = f"mypyvy-nightly-output-{format_datetime(self.start_time)}"
        if args.job_suffix is not None:
            output_dir_name += f'-{args.job_suffix}'
        self.output_dir = Path(output_dir_name)
        self.output_dir.mkdir(exist_ok=True)
        self.log_dir = self.output_dir / JOB_LOG_DIR
        self.log_dir.mkdir()

        self.global_logfile = open(self.output_dir / 'run-jobs.log', 'w')
        print(f'output in {self.output_dir}')
        self.log_global('mypyvy nightly starting')
        self.log_global(f'start_time={self.start_time}')
        self.log_global(f'args={sys.argv}')
        self.log_global(f'parsed args: {args}')
        self.log_global(f'mypyvy commit {get_mypyvy_sha()}')
        self.log_global('')

        self.collect_jobs()

    def collect_jobs(self) -> None:
        self.log_global('jobs:')
        self.jobs = []
        for example_file in sorted((args.mypyvy_path / 'examples').glob('*.pyv'), key=str):
            for seed in range(args.num_seeds):
                key = f'{seed:0{len(str(args.num_seeds - 1))}}' if args.num_seeds > 1 else None
                job = Job(example_file.stem, key,
                          ['updr', '--log=info', '--log-time'] +
                          ([f'--seed={seed}'] if args.num_seeds > 1 else []) +
                          [str(example_file)])
                self.log_global(f'  {job}')
                self.jobs.append(job)
        self.log_global('')

    def log(self, msg: str, logfile: IO[str]) -> None:
        print(format_datetime(datetime.now()), msg, file=logfile)

    def log_global(self, msg: str) -> None:
        self.log(msg, logfile=self.global_logfile)

    def run_job(self, job: Job) -> None:
        job_dir = self.log_dir if job.key is None else (self.log_dir / job.example_name)
        logfile_basename = job.example_name if job.key is None else (job.example_name + '-' + job.key)

        job_dir.mkdir(exist_ok=True)

        with open(job_dir / (logfile_basename + '.out'), 'w') as f_out, \
             open(job_dir / (logfile_basename + '.err'), 'w') as f_err, \
             open(job_dir / (logfile_basename + '.log'), 'w') as f_log:

            self.log(f'worker thread {threading.current_thread().name}', f_log)
            cmd = ['python3.8', '-u', str(args.mypyvy_path / 'src' / 'mypyvy.py')] + job.mypyvy_cmdline_args
            self.log(f'running command {" ".join(cmd)}', f_log)
            proc_start_time = datetime.now()
            try:
                proc = subprocess.run(cmd, stdout=f_out, stderr=f_err, text=True, timeout=args.job_timeout)
            except subprocess.TimeoutExpired:
                self.log('process timed out', f_log)
            else:
                self.log(f'proc returned {proc.returncode}', f_log)
            proc_end_time = datetime.now()
            self.log(f'{(proc_end_time - proc_start_time).total_seconds()} elapsed', f_log)

    def run_jobs(self) -> None:
        self.log_global('beginning to run mypyvy jobs')
        if args.num_threads is not None:
            num_workers = args.num_threads
        else:
            num_workers = max((os.cpu_count() or 1) - 1, 1)
        with concurrent.futures.ThreadPoolExecutor(max_workers=num_workers) as executor:
            fs = {}
            self.log_global('submitting jobs to queue')
            for job in self.jobs:
                fs[executor.submit(self.run_job, job)] = job
            self.log_global('jobs queued. waiting for completions...')
            for f in concurrent.futures.as_completed(fs):
                assert f.done()
                job = fs[f]
                self.log_global(f'completed {job}')
        self.log_global('done running mypyvy jobs')

def get_mypyvy_sha() -> str:
    return subprocess.run(['git', 'show-ref', '-s', 'HEAD'],
                          check=True, cwd=args.mypyvy_path, capture_output=True, text=True).stdout

@dataclass
class Result:
    name: str
    exit_msg: str
    time_msg: str
    out_msg: Optional[str] = dataclasses.field(default=None, init=False)

    def __str__(self) -> str:
        return f'{self.exit_msg} {self.time_msg}{(" " + self.out_msg) if self.out_msg is not None else ""}'

def analyze_results(output_dir: str) -> None:
    # example name -> key -> {log/out/err} -> Path
    files: Dict[str, Dict[str, Dict[str, Path]]] = collections.defaultdict(dict)
    for filename in (Path(output_dir) / JOB_LOG_DIR).iterdir():
        print(filename, filename.is_dir())

        if filename.is_dir():
            runs: Dict[str, Dict[str, Path]] = {}
            for f2 in filename.iterdir():
                key = f2.stem.rsplit('-', 1)[1]
                if key not in runs:
                    runs[key] = {}
                runs[key][f2.suffix] = f2
            files[filename.name] = runs
        else:
            if not files[filename.stem]:
                files[filename.stem] = {'0': {}}
            files[filename.stem]['0'][filename.suffix] = filename

    results = collections.defaultdict(list)
    output = []
    # max_stem_length = max(len(file) for file in files)
    for stem in sorted(files):
        rs = files[stem]
        output.append(f'{stem}:')
        for key in sorted(rs):
            output.append(f'  {key}:')
            r = rs[key]
            for suff in sorted(r):
                output.append(f'    {suff}')
                with open(r[suff]) as f:
                    lines = f.readlines()
                    for line in lines[-min(len(lines), 10):]:
                        output.append(f'      {line.strip()}')
                    if suff == '.log':
                        exit_msg = ' '.join(lines[-2].strip().split(' ')[1:])

                        time_msg = ' '.join(lines[-1].strip().split(' ')[1:])
                        result = Result(stem, exit_msg, time_msg)
                        results[stem].append(result)
                    elif suff == '.out':
                        assert result.name == stem
                        for line in lines:
                            l = line.strip()
                            if l == 'frame is safe and inductive. done!':
                                result.out_msg = 'safe'
                                break
                            elif (l == 'abstract counterexample: the system has no '
                                  'universal inductive invariant proving safety'):
                                result.out_msg = 'abstractly unsafe'

    with (Path(output_dir) / 'analysis.log').open('w') as analysis_log:
        for stem in sorted(results):
            res_list = results[stem]
            print(f'{stem}:', file=analysis_log)
            for res in res_list:
                print(f'  {res}', file=analysis_log)

        print('', file=analysis_log)
        for line in output:
            print(line, file=analysis_log)

def publish_results(output_dir: str) -> None:
    PUBLISH_PATH = '/var/www/dologale.jamesrwilcox.com/reports'
    if socket.gethostname() == 'dologale' and os.getcwd() != PUBLISH_PATH:
        shutil.move(output_dir, PUBLISH_PATH)

def main() -> None:
    parse_args()
    print(args)

    if not args.no_run:
        runner: Optional[JobRunner] = JobRunner(output_dir_name=args.output_directory)
        assert runner is not None
        runner.run_jobs()
    else:
        runner = None

    out_dir = args.output_directory
    if not out_dir:
        assert runner is not None
        out_dir = str(runner.output_dir)

    if not args.no_analyze:
        analyze_results(out_dir)

    if not args.no_publish:
        publish_results(out_dir)

if __name__ == '__main__':
    main()
