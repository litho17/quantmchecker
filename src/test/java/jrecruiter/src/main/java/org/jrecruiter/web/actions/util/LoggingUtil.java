/*
 * Copyright 2006-2014 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.jrecruiter.web.actions.util;

import java.io.File;
import java.util.Date;
import java.util.Iterator;
import java.util.List;

import org.jrecruiter.common.CollectionUtils;
import org.jrecruiter.web.actions.admin.LogFileInfo;
import org.slf4j.LoggerFactory;

import ch.qos.logback.classic.Logger;
import ch.qos.logback.classic.LoggerContext;
import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.core.Appender;
import ch.qos.logback.core.FileAppender;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * Contains utility methods to interact with the logback during runtime.
 *
 * @author Gunnar Hillert
 *
 */
public class LoggingUtil {

	/**
	 * re-defines the logback logging levels as a Java enumeration. This is quite
	 * helpful if you need to render the various log-levels as select-box. I wish
	 * logback @see {@link ch.qos.logback.classic.Level} would not use static variables
	 * but use enums instead.
	 *
	 * @author Gunnar Hillert
	 */
	public enum LogLevels {

		OFF(Integer.MAX_VALUE, "Off"),
		ERROR_INT(40000, "Error"),
		WARN_INT(30000, "Warn"),
		INFO_INT(20000, "Info"),
		DEBUG_INT(10000, "Debug"),
		TRACE(5000, "Trace"),
		ALL(Integer.MIN_VALUE, "All");

		private int logLevel;
		private String logLevelName;

		LogLevels(final int logLevel, final String logLevelName) {
			this.logLevel = logLevel;
			this.logLevelName = logLevelName;
		}

		public int getLogLevel() {
			return this.logLevel;
		}

		public String getLogLevelName() {
			return this.logLevelName;
		}

		public static LogLevels getLogLevelFromId(final int logLevelAsInt) {

			for (LogLevels logLevel : LogLevels.values()) {

				if (logLevelAsInt == logLevel.logLevel) {
					return logLevel;
				}
			}

			throw new IllegalStateException("Loglevel " + logLevelAsInt + " does not exist.");

		}

	}

	/**
	 * Retrieve all configured logback loggers.
	 *
	 * @param showAll If set return ALL loggers, not only the configured ones.
	 * @return List of Loggers
	 */
	public static List<ch.qos.logback.classic.Logger> getLoggers(final boolean showAll) {
		@Bound("LoggerFactory") int i;
		final LoggerContext lc = (LoggerContext) LoggerFactory.getILoggerFactory();
		@Inv("= (- loggers it) (- (+ c112 c109) c106)") final List<ch.qos.logback.classic.Logger> loggers = CollectionUtils.getArrayList();

		@Iter("<= it LoggerFactory") Iterator<Logger> it = lc.getLoggerList().iterator();
		ch.qos.logback.classic.Logger log;
		while (it.hasNext()) {
			c106: log = it.next();
			if(showAll == false) {
				if(log.getLevel() != null || LoggingUtil.hasAppenders(log)) {
					c109: loggers.add(log);
				}
			} else {
				c112: loggers.add(log);
			}
		}

		return loggers;
	}

	/**
	 * Get a single logger.
	 *
	 * @return Logger
	 */
	public static ch.qos.logback.classic.Logger getLogger(final String loggerName) {

		final LoggerContext lc = (LoggerContext) LoggerFactory.getILoggerFactory();

		return lc.getLogger(loggerName);

	}

	/**
	 * Test whether the provided logger has appenders.
	 *
	 * @param logger The logger to test
	 * @return true if the logger has appenders.
	 */
	public static boolean hasAppenders(ch.qos.logback.classic.Logger logger) {
		Iterator<Appender<ILoggingEvent>> it = logger.iteratorForAppenders();
		return it.hasNext();
	}

	/**
	 * Get the logfile information for the roor logger.
	 *
	 * @return List of LogFileInfo obejcts
	 */
	public static List<LogFileInfo> getLogFileInfos() {
		@Bound("LoggerFactory") int i;
		final LoggerContext lc = (LoggerContext) LoggerFactory.getILoggerFactory();

		@Inv("= (- logFileInfos it) (- c172 c160)") final List<LogFileInfo> logFileInfos = CollectionUtils.getArrayList();

		final Logger logger = lc.getLogger(Logger.ROOT_LOGGER_NAME);

		@Iter("<= it LoggerFactory") final Iterator<Appender<ILoggingEvent>> it = logger.iteratorForAppenders();

		while (it.hasNext()) {
			final Appender<ILoggingEvent> appender;
			c160: appender = it.next();

			if (appender instanceof FileAppender) {

				final FileAppender<ILoggingEvent> fileAppender = (FileAppender<ILoggingEvent>) appender;

				final File logFile = new File(fileAppender.getFile());
				final LogFileInfo logFileInfo = new LogFileInfo();

				logFileInfo.setFileName(logFile.getName());
				logFileInfo.setFileLastChanged(new Date(logFile.lastModified()));
				logFileInfo.setFileSize(logFile.length());
				c172: logFileInfos.add(logFileInfo);
			}

		}

		return logFileInfos;
	}

	/**
	 * Get the log file.
	 *
	 * @param logFileName The name of the log file
	 * @return The actual file
	 */
	public static File getLogFile(final String logFileName) {

		if (logFileName == null) {
			throw new IllegalArgumentException("logFileName cannot be null.");
		}

		final LoggerContext lc = (LoggerContext) LoggerFactory.getILoggerFactory();

		final Logger logger = lc.getLogger(Logger.ROOT_LOGGER_NAME);

		final Iterator<Appender<ILoggingEvent>> it = logger.iteratorForAppenders();

		while (it.hasNext()) {

			final Appender<ILoggingEvent> appender = it.next();

			if (appender instanceof FileAppender) {

				final FileAppender<ILoggingEvent> fileAppender = (FileAppender<ILoggingEvent>) appender;

				final File logFile = new File(fileAppender.getFile());

				if (logFile.getName().equalsIgnoreCase(logFileName)) {
					return logFile;
				}

			}

		}

		return null;
	}

}
