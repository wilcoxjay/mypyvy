
from argparse import ArgumentParser
import os, sys
from io import TextIOWrapper
from typing import List, Tuple

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.append(os.path.join(os.path.dirname(SCRIPT_DIR), 'src'))

from trace_tools import load_trace, Span
from matplotlib import pyplot as plt

def process_trace(trace: Span, prefix: str ='') -> None:
    with open('out.txt', 'w') as f:
        print(trace, file=f)

    fig = plt.figure()
    durations_remaining = []
    durations_sep = []
    total_solve = 0.0
    total_sep = 0.0
    for ig_query in trace.descendants('IG'):
        # print(ig_query, file = open('ig-query.txt', 'w'))
        # return
        if ig_query.data['rationale'] != 'learning':
            continue
        solve_phase = next(ig_query.descendants('Solve'))
        total_solve += solve_phase.duration
        for prefix_query in solve_phase.descendants('Pre'):
            if 'sep' in prefix_query.data:
                # t = 0.0
                # for x in prefix_query.descendants('Sep'):
                #     t += x.duration
                # print(f"{solve_phase.duration:0.3f} {prefix_query.duration:0.3f} {len(prefix_query.data['prefix'].linearize())} {t/prefix_query.duration:0.3f}")
                total_sep += prefix_query.duration
                durations_remaining.append(solve_phase.duration - prefix_query.duration)
                durations_sep.append(prefix_query.duration)
                # for x in prefix_query.descendants('SMT-tr'):
                    # print (f"{x.duration:0.3f}")

    print(f"Total IG time: {total_solve:0.3f}, prefix queries (sep only): {total_sep:0.3f}, percent: {total_sep/total_solve*100.0:0.1f}%")
    total = 0.0
    for push in trace.descendants('Push'):
        total += push.duration
    print(f"Total pushing time {total:0.3f}")
    print(f"Total time {trace.duration:0.3f}")
    

    plt.barh(range(len(durations_remaining)), durations_remaining, 0.8, label = 'Remaining')
    plt.barh(range(len(durations_remaining)), durations_sep, 0.8, label = 'Sep', left = durations_remaining)
    plt.gca().invert_yaxis()
    plt.legend()
    plt.xlabel('Time (wall-clock sec)')
    plt.ylabel('Query')
    plt.yticks([])
    for pos in ['right', 'top', 'bottom', 'left']:
        plt.gca().spines[pos].set_visible(False)
    plt.savefig(prefix+"ig-queries.png")

    fig, (ax1, ax2, ax3) = plt.subplots(nrows=3)

    durations_sat = []
    durations_unsat = []
    durations_unknown = []
    for ig_query in trace.descendants('IG'):
        for x in ig_query.descendants('SMT-tr'):
            if 'result' in x.data and str(x.data['result']) == 'sat':
                durations_sat.append(x.duration)
            elif 'result' in x.data and str(x.data['result']) == 'unsat':
                durations_unsat.append(x.duration)
            else:
                durations_unknown.append(x.duration)
    for ax, data, label in [(ax1, durations_sat, 'Sat'), (ax2, durations_unsat, 'Unsat'), (ax3, durations_unknown, 'Unk')]:
        ax.hist(data, log=True, bins=50, range = (0, 350))
        ax.set_title(label)
        for pos in ['right', 'top', 'bottom', 'left']:
            ax.spines[pos].set_visible(False)
    plt.tight_layout()
    plt.savefig(prefix+'sat-times.png')


    fig = plt.figure(figsize=(10,8))
    durations_scatter = []
    for index, ig_query in enumerate(trace.descendants('IG')):
        if ig_query.data['rationale'] != 'learning':
            continue
        solve_phase = next(ig_query.descendants('Solve'))
        for prefix_query in solve_phase.descendants('Pre'):
            code = 0 if 'unsep' in prefix_query.data else 1 if 'sep' in prefix_query.data else 2
            durations_scatter.append((index, prefix_query.duration, code))


    plt.scatter([i for (i, d, c) in durations_scatter if c == 0], [d for (i, d, c) in durations_scatter if c == 0], marker = 'x',  label='UNSEP')
    plt.scatter([i for (i, d, c) in durations_scatter if c == 2], [d for (i, d, c) in durations_scatter if c == 2], marker = 'o',  label='UNK')
    plt.scatter([i for (i, d, c) in durations_scatter if c == 1], [d for (i, d, c) in durations_scatter if c == 1], marker = 'd',  label='SEP')
    
    # plt.gca().invert_yaxis()
    plt.legend()
    plt.xlabel('Query')
    plt.xticks([])
    plt.ylabel('Time (wall-clock sec)')
    for pos in ['right', 'top']:
        plt.gca().spines[pos].set_visible(False)
    plt.gca().spines['bottom'].set_position('zero')
    plt.tight_layout()
    plt.savefig(prefix+"ig-queries-scatter.png")
    simulate(trace)

def simulate(trace: Span) -> None:
    total_original_time = 0.0
    total_work = 0.0
    for ig_query in trace.descendants('IG'):
        if ig_query.data['rationale'] != 'learning':
            continue
        solve_phase = next(ig_query.descendants('Solve'))
        prefixes = []
        for prefix in solve_phase.descendants('Pre'):
            prefixes.append((prefix.duration, 'sep' in prefix.data))
        original_time = sum(t for t, _ in prefixes)
        # print(prefixes)
        current: List[Tuple[float, bool]] = []
        time = 0.0
        work = 0.0
        K = 6
        success = False
        while True:
            # fill threads
            if len(current) < K and len(prefixes) > 0:
                current.append(prefixes.pop(0))
                continue
            # no more threads, exit
            if len(current) == 0:
                break
            min_index = min(range(len(current)), key=lambda i: current[i][0])

            finished_thread = current.pop(min_index)
            time_step = finished_thread[0]
            work += time_step * (len(current) + 1)
            time += time_step
            current = [(t - time_step, result) for (t, result) in current]
            if finished_thread[1]:
                success = True
                break
        print(f"IG query {success}, {time:0.3f}, {original_time:0.3f}, {work:0.3f}")
        total_original_time += original_time
        total_work += work
    print(f"Overall: {total_original_time:0.3f} {total_work:0.3f}")
    print(f"Ratio: {total_original_time/total_work:0.3f}")
    


def main() -> None:
    parser = ArgumentParser()
    parser.add_argument('--trace')
    parser.add_argument('--prefix', default = '')
    args = parser.parse_args()

    
    if args.trace.endswith('.pickle'):
        with open(args.trace, 'rb') as f:
            trace = load_trace(f)
            process_trace(trace, args.prefix)
    elif args.trace.endswith('.tar.gz'):
        import tarfile
        with tarfile.open(args.trace, 'r:*') as tf:
            main_log_stream = tf.extractfile('main.log')
            assert main_log_stream is not None
            print(f"Main log starts with: {TextIOWrapper(main_log_stream).readline().strip()}")
            
            trace = load_trace(tf.extractfile('trace.pickle'))
            process_trace(trace, args.prefix)

if __name__ == '__main__':
    main()