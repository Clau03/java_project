package tictactoe.src;

public interface BoardInterf {

    int index(int row, int col);

    boolean isField(int index);

    boolean isField(int row, int col);

    Mark getField(int i);

    Mark getField(int row, int col);

    boolean isEmptyField(int i);

    boolean isEmptyField(int row, int col);

    boolean isFull();

    boolean gameOver();

    boolean hasRow(Mark m);

    boolean hasColumn(Mark m);

    boolean hasDiagonal(Mark m);

    boolean isWinner(Mark m);

    boolean hasWinner();

    String toString();

    void reset();

    void setField(int i, Mark m);

    void setField(int row, int col, Mark m);
}
