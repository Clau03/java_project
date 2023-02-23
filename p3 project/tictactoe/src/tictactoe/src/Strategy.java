package tictactoe.src;

public interface Strategy {

    String getName();

    int determineMove(Board board, Mark mark);
}
