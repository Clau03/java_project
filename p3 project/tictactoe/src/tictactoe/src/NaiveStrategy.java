package tictactoe.src;

import java.util.ArrayList;
import java.util.List;

public class NaiveStrategy implements Strategy {

    @Override
    public String getName() {
        return "Naive Strategy";
    }

    @Override
    public int determineMove(Board board, Mark mark) {

        List<Integer> arrlist = new ArrayList<>();

        for (int i = 0; i < board.DIM * board.DIM; i++) {
            if (board.isEmptyField(i)) {
                arrlist.add(i);
            }
        }
        return arrlist.get((int) (Math.random() * (arrlist.size())));
    }

}
