// Création de la table

CREATE TABLE `runs` (
  `tool` text NOT NULL,
  `file` text NOT NULL,
  `toolDate` timestamp NULL DEFAULT NULL,
  `runDate` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `time` double NOT NULL,
  `mem` double NOT NULL,
  `result` text NOT NULL,
  `fullOutput` text NOT NULL,
  `timeAllowed` double NOT NULL,
  `memAllowed` double NOT NULL
) ENGINE=InnoDB DEFAULT CHARSET=latin1;

// Requêtes simples

SELECT tool,result,COUNT(*) FROM runs WHERE result != 'timeout' GROUP BY tool,result
SELECT tool,COUNT(*) FROM runs WHERE result != 'timeout' GROUP BY tool
SELECT tool,result,COUNT(*) FROM runs GROUP BY tool,result
SELECT tool,COUNT(*) FROM runs GROUP BY tool

// Search for errors (two tools with different results)

SELECT sub.file FROM (SELECT file,COUNT(DISTINCT result) as count FROM runs WHERE result != 'timeout' GROUP BY file) AS sub WHERE count > 1
