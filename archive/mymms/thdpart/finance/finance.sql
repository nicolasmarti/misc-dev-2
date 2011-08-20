-- phpMyAdmin SQL Dump
-- version 3.1.2deb1ubuntu0.1
-- http://www.phpmyadmin.net
--
-- Host: localhost
-- Generation Time: Aug 02, 2009 at 05:58 PM
-- Server version: 5.0.75
-- PHP Version: 5.2.6-3ubuntu4.1

SET SQL_MODE="NO_AUTO_VALUE_ON_ZERO";

--
-- Database: `finance`
--

-- --------------------------------------------------------

--
-- Table structure for table `ibcontract`
--

CREATE TABLE IF NOT EXISTS `ibcontract` (
  `cid` int(11) NOT NULL auto_increment,
  `symbol` varchar(10) NOT NULL,
  `type` enum('STK','OPT','FUT','IND','FOR','CASH','BAG') NOT NULL,
  `expiry` date default NULL,
  `strike` double default NULL,
  `right` enum('PUT','CALL') default NULL,
  `exchange` varchar(10) NOT NULL,
  `currency` varchar(5) default NULL,
  `active` tinyint(1) NOT NULL,
  PRIMARY KEY  (`cid`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 AUTO_INCREMENT=1 ;

--
-- Dumping data for table `ibcontract`
--


-- --------------------------------------------------------

--
-- Table structure for table `iborder`
--

CREATE TABLE IF NOT EXISTS `iborder` (
  `oid` int(11) NOT NULL auto_increment,
  `action` enum('BUY','SELL','SSHORT') NOT NULL,
  `totalquantity` bigint(20) NOT NULL,
  `ordertype` enum('MKT','MKTCLS','LMT','LMTCLS','PEGMKT','STP','STPLMT','TRAIL','REL','VWAP') NOT NULL,
  `lmtprice` double NOT NULL,
  `tif` enum('DAY','GTC','GTD','IOC','OPG') NOT NULL,
  `openclose` enum('O','C') NOT NULL,
  `status` enum('Pending','PendingSubmitted','PendingCancel','PreSubmitted','Submitted','Cancelled','Filled') NOT NULL,
  `pending` int(11) NOT NULL,
  PRIMARY KEY  (`oid`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 AUTO_INCREMENT=1 ;

--
-- Dumping data for table `iborder`
--


-- --------------------------------------------------------

--
-- Table structure for table `ibquoteprice`
--

CREATE TABLE IF NOT EXISTS `ibquoteprice` (
  `date` datetime NOT NULL,
  `cid` int(11) NOT NULL,
  `type` enum('BID','ASK','LAST','HIGH','LOW','CLOSE') NOT NULL,
  `value` double NOT NULL
) ENGINE=MyISAM DEFAULT CHARSET=latin1;

--
-- Dumping data for table `ibquoteprice`
--


-- --------------------------------------------------------

--
-- Table structure for table `ibquotesize`
--

CREATE TABLE IF NOT EXISTS `ibquotesize` (
  `date` datetime NOT NULL,
  `cid` int(11) NOT NULL,
  `type` enum('BID','ASK','LAST','VOLUME') NOT NULL,
  `value` bigint(20) NOT NULL
) ENGINE=MyISAM DEFAULT CHARSET=latin1;

--
-- Dumping data for table `ibquotesize`
--


-- --------------------------------------------------------

--
-- Table structure for table `orderexec`
--

CREATE TABLE IF NOT EXISTS `iborderexec` (
  `id` bigint(20) NOT NULL auto_increment,
  `oid` bigint(20) NOT NULL,
  `size` int(11) NOT NULL,
  `price` double NOT NULL,
  `date` datetime NOT NULL,
  PRIMARY KEY  (`id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 AUTO_INCREMENT=1 ;

--
-- Dumping data for table `orderexec`
--


