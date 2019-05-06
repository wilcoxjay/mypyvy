import argparse

def dump(N: int, mode: str) -> None:
    assert N >= 2
    assert mode in ['short', 'long']


    with open('micro.{}.pvy'.format(N), 'w') as f:

        def declare_msgs() -> None:
            for i in range(1,N+1):
                print("mutable relation p{}a_msg(node)".format(i), file=f)
                print("mutable relation p{}b_msg(node)".format(i), file=f)

        def initialize_msgs() -> None:
            for i in range(1,N+1):
                print("init !p{}a_msg(N)".format(i), file=f)
                print("init !p{}b_msg(N)".format(i), file=f)


        def define_msg_actions() -> None:
            for i in range(1,N+1):
                print("", file=f)
                print("transition send_{}a(n: node) {{".format(i), file=f)
                if i > 1:
                    print("    assume p{}b_msg(N);".format(i-1), file=f)
                print("    p{}a_msg(n) := true;".format(i), file=f)
                print("}", file=f)
                print("", file=f)
                print("transition send_{}b(n: node) {{".format(i), file=f)
                print("    assume p{}a_msg(n);".format(i), file=f)
                print("    p{}b_msg(n) := true;".format(i), file=f)
                print("}", file=f)

        print("sort node", file=f)
        print("", file=f)
        declare_msgs()
        print("", file=f)
        print("mutable relation done", file=f)
        print("", file=f)
        initialize_msgs()
        print("init !done", file=f)
        define_msg_actions()
        print("", file=f)
        print("transition finish() {", file=f)
        print("    assume p{}b_msg(N);".format(N), file=f)
        print("    done := true;", file=f)
        print("}", file=f)
        print("", file=f)
        print("safety done -> p1a_msg(N)", file=f)
        print("", file=f)
        print("# {}".format(mode), file=f)
        print("automaton {", file=f)
        print("  init phase p1", file=f)
        print("", file=f)
        print("  global", file=f)
        print("    safety done -> p1a_msg(N)", file=f)
        print("    transition send_1a -> self", file=f)
        print("    transition send_1b -> self", file=f)
        print("", file=f)
        print("  phase p1", file=f)
        print("    transition send_2a -> phase p2", file=f)

        if mode == 'short':
            print("", file=f)
            print("  phase p2", file=f)
            for i in range(2, N+1):
                print("    transition send_{}a -> self".format(i), file=f)
                print("    transition send_{}b -> self".format(i), file=f)
            print("    transition finish -> self", file=f)            
        else:
            for i in range(2, N+1):
                print("", file=f)
                print("  phase p{}".format(i), file=f)

                for j in range(2, i+1):
                    print("    transition send_{}a -> self".format(j), file=f)
                    print("    transition send_{}b -> self".format(j), file=f)

                if i < N:
                    print("    transition send_{}a -> phase p{}".format(i+1, i+1), file=f)
                else:
                    print("    transition finish -> self", file=f)

        print("}", file=f)



def main() -> None:
    argparser = argparse.ArgumentParser()
    argparser.add_argument('--mode', default='short', choices=['short', 'long'],
                           help='whether to use an automaton with 2 or N states')
    argparser.add_argument('N', type=int, default=2, help='number of phases in protocol')

    args = argparser.parse_args()

    dump(args.N, args.mode)

if __name__ == '__main__':
    main()
