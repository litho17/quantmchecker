package braidit_1.com.cyberpointllc.stac.dispatch;

import braidit_1.com.cyberpointllc.stac.communications.CommunicationsConnection;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsException;
import braidit_1.com.cyberpointllc.stac.communications.CommunicationsManager;
import braidit_1.com.cyberpointllc.stac.console.Display;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Summary;

import java.io.IOException;
import java.util.Objects;
import java.util.Queue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

/**
 * Allows messages and console commands to be processed in the order
 * that they are received.  This is accomplished by having all console
 * commands and all remote messages (including connect and disconnect)
 * executed in a single-thread pool.  To ensure the user is notified
 * of all errors, the console is run in a separate (single-)thread-pool
 * and the calling thread is left in a loop that periodically polls for
 * any generated errors.
 */
public abstract class Dispatcher implements CommunicationsManager {
    private static final long POLL_TIME = 1;

    protected final Display display;

    private final @InvUnk("Complex control flow due to thread scheduling") BlockingQueue<Throwable> errorQueue;
    private final ExecutorService displayExecutorService;
    private final ScheduledExecutorService scheduledExecutorService;

    public Dispatcher(Display display) {
        this.display = Objects.requireNonNull(display, "Console may not be null");

        errorQueue = new LinkedBlockingQueue<>();
        displayExecutorService = Executors.newSingleThreadExecutor();
        scheduledExecutorService = new MyScheduledThreadPoolExecutor(errorQueue);
    }

    // There are three abstract methods to be implemented.
    // These allow for application-specific handling of
    // received messages, connections, and disconnections,
    // when it is their turn to be processed.

    protected abstract void handleReceivedMessage(byte[] data, CommunicationsConnection conn);

    protected abstract void handleNewConnection(CommunicationsConnection conn) throws CommunicationsException;

    protected abstract void handleClosedConnection(CommunicationsConnection conn) throws CommunicationsException;

    /**
     * Creates and executes a one-shot action that becomes enabled
     * after the given delay.
     *
     * @param command the task to execute
     * @param delay   the time from now to delay execution
     * @param unit    the time unit of the delay parameter
     * @return a ScheduledFuture representing pending completion of
     * the task and whose {@code get()} method will return
     * {@code null} upon completion
     * @throws RejectedExecutionException if the task cannot be
     *                                    scheduled for execution
     * @throws NullPointerException       if command is null
     * @see ScheduledExecutorService#schedule(Runnable, long, TimeUnit)
     */
    public ScheduledFuture<?> schedule(Runnable command, long delay, TimeUnit unit) {
        return scheduledExecutorService.schedule(command, delay, unit);
    }

    /**
     * Creates and executes a ScheduledFuture that becomes enabled after the
     * given delay.
     *
     * @param callable the function to execute
     * @param delay    the time from now to delay execution
     * @param unit     the time unit of the delay parameter
     * @param <V>      the type of the callable's result
     * @return a ScheduledFuture that can be used to extract result or cancel
     * @throws RejectedExecutionException if the task cannot be
     *                                    scheduled for execution
     * @throws NullPointerException       if callable is null
     * @see ScheduledExecutorService#schedule(Callable, long, TimeUnit)
     */
    public <V> ScheduledFuture<V> schedule(Callable<V> callable, long delay, TimeUnit unit) {
        return scheduledExecutorService.schedule(callable, delay, unit);
    }

    /**
     * Creates and executes a periodic action that becomes enabled first
     * after the given initial delay, and subsequently with the given
     * period; that is executions will commence after
     * {@code initialDelay} then {@code initialDelay+period}, then
     * {@code initialDelay + 2 * period}, and so on.
     * If any execution of the task
     * encounters an exception, subsequent executions are suppressed.
     * Otherwise, the task will only terminate via cancellation or
     * termination of the executor.  If any execution of this task
     * takes longer than its period, then subsequent executions
     * may start late, but will not concurrently execute.
     *
     * @param command      the task to execute
     * @param initialDelay the time to delay first execution
     * @param period       the period between successive executions
     * @param unit         the time unit of the initialDelay and period parameters
     * @return a ScheduledFuture representing pending completion of
     * the task, and whose {@code get()} method will throw an
     * exception upon cancellation
     * @throws RejectedExecutionException if the task cannot be
     *                                    scheduled for execution
     * @throws NullPointerException       if command is null
     * @throws IllegalArgumentException   if period less than or equal to zero
     * @see ScheduledExecutorService#scheduleAtFixedRate(Runnable, long, long, TimeUnit)
     */
    public ScheduledFuture<?> scheduleAtFixedRate(Runnable command,
                                                  long initialDelay,
                                                  long period,
                                                  TimeUnit unit) {
        return scheduledExecutorService.scheduleAtFixedRate(command, initialDelay, period, unit);
    }

    /**
     * Creates and executes a periodic action that becomes enabled first
     * after the given initial delay, and subsequently with the
     * given delay between the termination of one execution and the
     * commencement of the next.  If any execution of the task
     * encounters an exception, subsequent executions are suppressed.
     * Otherwise, the task will only terminate via cancellation or
     * termination of the executor.
     *
     * @param command      the task to execute
     * @param initialDelay the time to delay first execution
     * @param delay        the delay between the termination of one
     *                     execution and the commencement of the next
     * @param unit         the time unit of the initialDelay and delay parameters
     * @return a ScheduledFuture representing pending completion of
     * the task, and whose {@code get()} method will throw an
     * exception upon cancellation
     * @throws RejectedExecutionException if the task cannot be
     *                                    scheduled for execution
     * @throws NullPointerException       if command is null
     * @throws IllegalArgumentException   if delay less than or equal to zero
     * @see ScheduledExecutorService#scheduleWithFixedDelay(Runnable, long, long, TimeUnit)
     */
    public ScheduledFuture<?> scheduleWithFixedDelay(Runnable command,
                                                     long initialDelay,
                                                     long delay,
                                                     TimeUnit unit) {
        return scheduledExecutorService.scheduleWithFixedDelay(command, initialDelay, delay, unit);
    }

    @Override
    public void handle(CommunicationsConnection conn, byte[] message) throws CommunicationsException {
        try {
            scheduledExecutorService.submit(new MessageManager(conn, message));
        } catch (RejectedExecutionException e) {
            if (!scheduledExecutorService.isShutdown()) {
                throw new CommunicationsException("Trouble submitting remote message task", e);
            }
        }
    }

    @Override
    public void newConnection(CommunicationsConnection connection) throws CommunicationsException {
        if (connection != null) {
            try {
                Future<?> future = scheduledExecutorService.submit(new NewConnectionManager(connection));
                // Need to wait for this command (and any pending messages)
                // to get executed before allowing another command
                future.get();
            } catch (ExecutionException e) {
                if (e.getCause() instanceof CommunicationsException) {
                    throw (CommunicationsException) e.getCause();
                } else {
                    throw new CommunicationsException(e.getCause());
                }
            } catch (RejectedExecutionException e) {
                if (!scheduledExecutorService.isShutdown()) {
                    throw new CommunicationsException("Trouble submitting new connection task", e);
                }
            } catch (Exception e) {
                throw new CommunicationsException(e);
            }
        }
    }

    @Override
    public void closedConnection(CommunicationsConnection connection) throws CommunicationsException {
        try {
            scheduledExecutorService.submit(new ClosedConnectionManager(connection));
        } catch (RejectedExecutionException e) {
            if (!scheduledExecutorService.isShutdown()) {
                throw new CommunicationsException("Trouble submitting close connection task", e);
            }
        }
    }

    /**
     * Runs all commands and messages in the calling thread.
     * All console commands are parsed and launched in a
     * background thread so the processing of the commands
     * and messages can be handled in the calling thread.
     * This allows the caller to be notified of background
     * processing errors.
     *
     * @throws Throwable if there are processing errors
     */
    public void run() throws Throwable {
        displayExecutorService.execute(new DisplayRunner());

        // While waiting for the console to conclude,
        // process the results of all background dispatches in the
        // main thread so the user can be notified of any issues.
        while (!display.shouldExit()) {
            try {
                Throwable throwable = errorQueue.poll(POLL_TIME, TimeUnit.SECONDS);

                if (throwable != null) {
                    throw throwable;
                }
            } catch (InterruptedException e) {
                System.err.println("Error polling interrupted");
            }
        }
    }

    /**
     * Handles any remaining console messages, then shuts down
     */
    public void shutdown() {
        display.setShouldExit(true);
        displayExecutorService.shutdown();
        scheduledExecutorService.shutdown();
    }

    private class DisplayRunner implements Runnable {
        @Override
        public void run() {
            while (!display.shouldExit()) {
                try {
                    String command = display.pullEnsuingCommand();
                    Future<?> future = scheduledExecutorService.submit(new CommandManager(command));
                    // Need to wait for this command (and any pending messages)
                    // to get executed before allowing another command
                    future.get();
                } catch (ExecutionException e) {
                    errorQueue.add(new CommunicationsException(e.getCause()));
                } catch (RejectedExecutionException e) {
                    if (scheduledExecutorService.isShutdown()) {
                        display.setShouldExit(true);
                    } else {
                        errorQueue.add(new CommunicationsException("Trouble submitting console task", e));
                    }
                } catch (Exception e) {
                    errorQueue.add(e);
                }
            }
        }
    }

    private class NewConnectionManager implements Callable<Void> {
        private final CommunicationsConnection connection;

        private NewConnectionManager(CommunicationsConnection connection) {
            this.connection = connection;
        }

        @Override
        public Void call() throws Exception {
            handleNewConnection(connection);
            return null;
        }
    }

    private class ClosedConnectionManager implements Runnable {
        private final CommunicationsConnection connection;

        private ClosedConnectionManager(CommunicationsConnection connection) {
            this.connection = connection;
        }

        @Override
        public void run() {
            try {
                handleClosedConnection(connection);
            } catch (@InvUnk("Extend library class") CommunicationsException e) {
                System.err.println("Error disconnecting: " + e.getMessage());
            }
        }
    }

    /**
     * Handles the commands from the console.
     */
    private class CommandManager implements Runnable {
        private final String command;

        private CommandManager(String command) {
            this.command = command;
        }

        @Override
        public void run() {
            try {
                display.executeCommand(command);
            } catch (IOException e) {
                System.err.println("Error executing command: " + e.getMessage());
            }
        }
    }

    /**
     * Handles the messages that are received from
     * a remote connection.
     */
    private class MessageManager implements Runnable {
        private final CommunicationsConnection conn;
        private final byte[] data;

        private MessageManager(CommunicationsConnection conn, byte[] data) {
            this.conn = conn;
            this.data = data;
        }

        @Override
        public void run() {
            try {
                handleReceivedMessage(data, conn);
            } catch (Exception e) {
                System.err.println("Error parsing message: " + e.getMessage());
            }
        }
    }

    private static class MyScheduledThreadPoolExecutor extends ScheduledThreadPoolExecutor {
        private final Queue<Throwable> queue;

        MyScheduledThreadPoolExecutor(Queue<Throwable> queue) {
            super(1);

            this.queue = Objects.requireNonNull(queue, "Queue may not be null");
        }

        @Override
        @Summary({"queue", "1"})
        protected void afterExecute(Runnable runnable, Throwable throwable) {
            super.afterExecute(runnable, throwable);

            if ((throwable == null) && (runnable instanceof Future<?>)) {
                try {
                    ((Future<?>) runnable).get();
                } catch (CancellationException e) {
                    throwable = e;
                } catch (ExecutionException e) {
                    throwable = e.getCause();
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt(); // ignore/reset
                }
            }

            if (throwable != null) {
                queue.add(throwable);
            }
        }
    }
}
