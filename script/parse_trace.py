
from argparse import ArgumentParser
import os, sys, json
from io import TextIOWrapper
from typing import List, Tuple

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
sys.path.append(os.path.join(os.path.dirname(SCRIPT_DIR), 'src'))

from trace_tools import load_trace, Span
from matplotlib import pyplot as plt

def process_trace(trace: Span, prefix: str ='') -> None:
    # with open(f'{prefix}out.txt', 'w') as f:
    #     print(trace, file=f)

    durations_remaining = []
    durations_sep = []
    n_smt = 0
    total_solve = 0.0
    total_successful_prefix_time = 0.0
    total_sep_query = 0.0
    total_eval_query = 0.0
    total_smt_query = 0.0
    for ig_query in trace.descendants('IG'):
        # print(ig_query, file = open('ig-query.txt', 'w'))
        # return
        if ig_query.data['rationale'] != 'learning':
            continue
        # print(ig_query, file = open('ig-query.txt', 'w'))
        solve_phase = next(ig_query.descendants('Solve'))
        total_solve += solve_phase.duration
        for prefix_query in solve_phase.descendants('Pre'):

            time_eval = 0.0
            time_sep = 0.0
            core = 0
            for sep_query in prefix_query.descendants('Sep'):
                if 'time_eval' in sep_query.data:
                    time_eval = sep_query.data['time_eval']
                if 'time_sep' in sep_query.data:
                    time_sep = sep_query.data['time_sep']
                if 'core' in sep_query.data:
                    core = sep_query.data['core']

            time_smt = sum(x.duration for x in prefix_query.descendants('SMT-tr'))
            n_smt += sum(1 for x in prefix_query.descendants('SMT-tr'))

            if 'sep' in prefix_query.data:
                total_sep_query += time_sep
                total_eval_query += time_eval
                total_smt_query += time_smt

            if 'sep' in prefix_query.data:

                # t = 0.0
                # for x in prefix_query.descendants('Sep'):
                #     t += x.duration
                # print(f"{solve_phase.duration:0.3f} {prefix_query.duration:0.3f} {len(prefix_query.data['prefix'].linearize())} {t/prefix_query.duration:0.3f}")

                
                total_successful_prefix_time += prefix_query.duration
                durations_remaining.append(solve_phase.duration - prefix_query.duration)
                durations_sep.append(prefix_query.duration)
                prefix_value = prefix_query.data['prefix']
                pre_pp = " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + f'{sort_i}.' for (fa, sort_i) in prefix_value.linearize())
                # print(f"{ig_query.instance}, {ig_query.duration:> 10.3f}, {prefix_query.data['category']}, {pre_pp} {core}")
                # print(f"{ig_query.instance}, {ig_query.duration:> 10.3f}, {prefix_query.data['category']}, {pre_pp}")
                break
        else:
            durations_remaining.append(solve_phase.duration)
            durations_sep.append(0)
                
    if False:
        longest_queries = list(sorted([ig_query for ig_query in trace.descendants('IG') if ig_query.data['rationale'] == 'learning'], reverse=True, key = lambda q: q.duration)[:5])
        for ig_query in longest_queries:
            print(ig_query.instance, ig_query.duration)
            solve_phase = next(ig_query.descendants('Solve'))
            
            if (solution := next((prefix_query for prefix_query in solve_phase.descendants('Pre') if 'sep' in prefix_query.data), None)) is not None:
                for sep in solution.descendants('Sep'):
                    pass
                pre_pp = " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + f'{sort_i}.' for (fa, sort_i) in solution.data['prefix'].linearize())
                print(f"Solution {solution.duration:0.3f} {sep.data['core']:> 4} {pre_pp}")
                
            longest_prefixes = list(sorted([p for p in solve_phase.descendants('Pre')], reverse=True, key = lambda q: q.duration)[:20])
            for p in longest_prefixes:
                pre_pp = " ".join(('A' if fa == True else 'E' if fa == False else 'Q') + f'{sort_i}.' for (fa, sort_i) in p.data['prefix'].linearize())
                max_core = 0
                t = 0.0
                for sep in p.descendants('Sep'):
                    t += sep.duration
                    max_core = max(max_core, sep.data.get('core', 0))
                print(f"{p.duration:> 10.3f} {max_core: >4} {100.0*t/p.duration:4.1f}% {pre_pp}")
                longest_smt = list(sorted([s for s in p.descendants('SMT-tr')], reverse=True, key = lambda q: q.duration)[:10])
                for smt in longest_smt:
                    print(f"    {smt.duration:> 10.3f} {smt.data.get('result', 'unknown')}")

    print(f"Total time {trace.duration:0.3f}")
    print(f"Total learning IG time: {total_solve:0.3f}")
    print(f"Learning prefix queries (success only): {total_successful_prefix_time:0.3f} {total_successful_prefix_time/total_solve*100.0:>4.1f}%")
    print(f"Total sep. algo time {total_sep_query:0.3f}\t{100.0*total_sep_query/total_successful_prefix_time:>4.1f}%")
    print(f"Total eval time      {total_eval_query:0.3f}\t{100.0*total_eval_query/total_successful_prefix_time:>4.1f}%")
    print(f"Total smt time       {total_smt_query:0.3f}\t{100.0*total_smt_query/total_successful_prefix_time:>4.1f}%")
    total_overhead = total_successful_prefix_time - (total_sep_query + total_eval_query + total_smt_query)
    print(f"Total overhead time  {total_overhead:0.3f}\t{100.0*total_overhead/total_successful_prefix_time:>4.1f}%")
    
    total_push = 0.0
    imblocker = 0.0
    former = 0.0
    smtpush = 0.0
    redundancy = 0.0
    for push in trace.descendants('Push'):
        total_push += push.duration
        imblocker += sum(d.duration for d in push.descendants("ImBlocker"))
        former += sum(d.duration for d in push.descendants("Former"))
        smtpush += sum(d.duration for d in push.descendants("SMTpush"))
        redundancy += sum(d.duration for d in push.descendants("Redundancy"))
    print(f"Total pushing time {total_push:0.3f}")
    print(f"  ImBlocker  {100.0 * imblocker / total_push:>4.1f}%")
    print(f"  Former     {100.0 * former / total_push:>4.1f}%")
    print(f"  SMTPush    {100.0 * smtpush / total_push:>4.1f}%")
    print(f"  Redundancy {100.0 * redundancy / total_push:>4.1f}%")
    print(f"  Overhead   {100.0 * (total_push - (imblocker + former + smtpush + redundancy)) / total_push:>4.1f}%")
    

    # print(json.dumps({
    #     'n_queries': len(durations_remaining),
    #     'total_sep': total_successful_prefix_time,
    #     'total_smt': total_smt_query,
    #     'n_smt': n_smt,        
    # }))
    return

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
        for sep in ig_query.descendants('SMT-tr'):
            if 'result' in sep.data and str(sep.data['result']) == 'sat':
                if sep.duration > 6:
                    durations_sat.append(sep.duration)
            elif 'result' in sep.data and str(sep.data['result']) == 'unsat':
                durations_unsat.append(sep.duration)
            else:
                durations_unknown.append(sep.duration)
    for ax, data, label in [(ax1, durations_sat, 'Sat'), (ax2, durations_unsat, 'Unsat'), (ax3, durations_unknown, 'Unknown')]:
        bins = 50
        accum = [0.0] * bins
        spacing = 300/float(bins)
        cutoffs = [i*spacing for i in range(bins)]
        for d in data:
            if d < cutoffs[0]:
                accum[0] += d
                continue
            for i in range(1, bins):
                if d < cutoffs[i]:
                    accum[i-1] += d
                    break
            else:
                accum[-1] += d

        ax.bar(cutoffs, accum, width=spacing, align='edge')
        # ax.hist(data, log=True, bins=50, range = (0, 350))
        ax.set_title(label)
        ax.set_ylabel('Total time')
        ax.set_xlabel('Query duration')
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
    # simulate(trace)

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