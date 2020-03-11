from datetime import datetime
from pathlib import Path
import subprocess
import sys

from typing import Optional

MYPYVY_PATH = Path.home() / 'build' / 'mypyvy'

class Nightly:
    def __init__(self, output_dir_name: Optional[str] = None) -> None:
        self.start_time = datetime.now()
        if output_dir_name is None:
            output_dir_name = f"mypyvy-nightly-output-{self.start_time.strftime('%Y%m%d-%H%M%S')}"
        self.output_dir = Path(output_dir_name)
        self.output_dir.mkdir()
        self.log_file = open(self.output_dir / 'log', 'w')
        self.log('mypyvy nightly starting')
        self.log(f'start_time={self.start_time}')
        self.log(f'args={sys.argv}')
        self.log(f'mypyvy commit {get_mypyvy_sha()}')
        self.log('')

    def log(self, msg: str) -> None:
        print(msg, file=self.log_file)

    def collect_data(self) -> None:
        for example_filename in (MYPYVY_PATH / 'examples').glob('*.pyv'):
            cmd = ['python3.8', str(MYPYVY_PATH / 'src' / 'mypyvy.py'), 'updr', '--log=info', str(example_filename)]
            self.log(f'running command {" ".join(cmd)}')
            proc_start_time = datetime.now()
            with open(self.output_dir / (example_filename.stem + '.out'), 'w') as f_out, \
                 open(self.output_dir / (example_filename.stem + '.err'), 'w') as f_err:
                try:
                    proc = subprocess.run(cmd, stdout=f_out, stderr=f_err, text=True, timeout=3)
                except subprocess.TimeoutExpired:
                    self.log('process timed out')
                else:
                    self.log(f'proc returned {proc.returncode}')
            proc_end_time = datetime.now()
            self.log(f'{(proc_end_time - proc_start_time).total_seconds()} elapsed')

    def create_report(self) -> None:
        pass

    def publish_report(self) -> None:
        pass

def update_mypyvy() -> None:
    print('not updating mypyvy during development')

    # subprocess.run(['git', 'fetch'], check=True, cwd=MYPYVY_PATH)
    # subprocess.run(['git', 'checkout', 'master'], check=True, cwd=MYPYVY_PATH)
    # subprocess.run(['git', 'reset', '--hard', 'origin/master'], check=True, cwd=MYPYVY_PATH)

def get_mypyvy_sha() -> str:
    return subprocess.run(['git', 'show-ref', '-s', 'refs/heads/master'],
                          check=True, cwd=MYPYVY_PATH, capture_output=True, text=True).stdout

def main() -> None:
    update_mypyvy()

    nightly = Nightly()
    nightly.collect_data()
    nightly.create_report()
    nightly.publish_report()

if __name__ == '__main__':
    main()
