import numpy as np
np.set_printoptions(precision=16, linewidth=np.inf)
from itertools import combinations

def stepmother_move(state, c):
    """
    The stepmother's move in the game.

    The stepmother can choose to divide 1 unit of water into arbitrary parts
    and pour them into the buckets.

    Parameters
    ----------
    state : list
        The current state of the buckets.
    c : float
        The volume of the buckets.

    Returns
    -------
    state : list
        The new state of the buckets after the stepmother's move.
    """
    if np.any(state + 1 > c):
        # The stepmother can make one of the buckets overflow.
        # Add 1 unit of water to the max bucket.
        max_bucket = np.argmax(state)
        state[max_bucket] += 1
    else:
        # The stepmother cannot win in this move.
        # (Possibly) best policy: 
        #     - Choose two buckets with the highest water level, that are not consecutive.
        #     - Pour the unit of water into the two buckets s.t. the water level is equal.
        bucket_pairs = list(combinations(range(5), 2))
        is_consecutive = lambda x: (max(x) + 1) % 5 == min(x) or (min(x) + 1) % 5 == max(x)
        max_pair = max(bucket_pairs, key=lambda x: state[x[0]] + state[x[1]] 
                       if not is_consecutive(x) else -1)
        
        goal_level = (state[max_pair[0]] + state[max_pair[1]] + 1) / 2
        state[max_pair[0]] = goal_level
        state[max_pair[1]] = goal_level

    return state


def cinderella_move(state):
    """
    Cinderella's move in the game.

    Cinderella can choose 2 consecutive buckets and pour the water from them out.

    Parameters
    ----------
    state : list
        The current state of the buckets.

    Returns
    -------
    state : list
        The new state of the buckets after Cinderella's move.
    """
    # Choose two consecutive buckets with max fill containing the absolute max bucket.
    max_bucket = np.argmax(state)
    neighbors = ((max_bucket - 1) % 5, (max_bucket + 1) % 5)
    max_neighbor = max(neighbors, key=lambda x: state[x])

    state[max_bucket] = 0
    state[max_neighbor] = 0

    return state


def check_win(state, c):
    """
    Check if the stepmother has won the game.

    The stepmother wins if she can make one of the buckets overflow.

    Parameters
    ----------
    state : list
        The current state of the buckets.

    Returns
    -------
    win : bool
        True if the stepmother has won, False otherwise.
    """
    return np.any(state > c)


def play_game(c = 1.5, limit = 10000):
    """
    Play the cinderella-stepmother game.

    Returns
    -------
    winner : str
        The winner of the game.
    """
    state = np.zeros(5, dtype=np.float64)
    print_state = lambda x: np.array([f"{y:.8f}" for y in x])

    for i in range(limit):
        state = stepmother_move(state, c)

        print(f'State after stepmother move {i + 1:{len(str(limit))}}: {print_state(state)}')

        if check_win(state, c):
            return f'Stepmother wins after {i + 1} moves.'

        state = cinderella_move(state)
        print(f'State after Cinderella move {i + 1:{len(str(limit))}}: {print_state(state)}')

    return f'Cinderella does not lose after {limit} moves.'


if __name__ == '__main__':
    from argparse import ArgumentParser

    parser = ArgumentParser()
    parser.add_argument('-c', '--volume', type=float, default=1.76, help='Volume of the buckets.')
    parser.add_argument('-l', '--limit', type=int, default=10000, help='Maximum of moves to play.')
    args = parser.parse_args()

    print(play_game(args.volume, args.limit))
