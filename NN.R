###########Author: Elnaz S Nobari,February 2018###################
##########version 1###########################


install.packages("quadprog")
install.packages("BLCOP")
install.packages("MASS")
install.packages("xlsx")


library("quadprog")
library(BLCOP) 
library("MASS")
library(xlsx)
install.packages("ggExtra")
library(ggExtra)
install.packages("GGally")
library(GGally)


devtools::install_github("kassambara/ggcorrplot")
library(ggcorrplot)
install.packages("portfolio")

library(portfolio)
install.packages("ggplot2")
library(ggplot2)

install.packages("devtools")
library(devtools)
install_github("vqv/ggbiplot")
install.packages("ggbiplot")

library(ggbiplot)

install.packages("XLConnect")
install.packages("data.table")
library(XLConnect)
library(data.table)
install.packages("dplyr")
library(dplyr)

install.packages("htmlTable")
library("htmlTable")
install.packages("ReporteRs")
library(ReporteRs)

library(magrittr)

install.packages("lubridate")
library(lubridate)

install.packages("matrixStats")
library(matrixStats)

install.packages("microbenchmark")
library("microbenchmark")

install.packages("factoextra")
library("factoextra")
install.packages("pryr")
library(pryr)
install.packages("caret")
install.packages("e1071")
library(e1071)
library(caret)

require(gridExtra)
library(ReporteRs)

install.packages("prodlim")
library(prodlim)

require(reshape2)
library(gridExtra)

install.packages("compare")
library(compare)
install.packages("tseries")
library(tseries)
install.packages("roll")
library("roll")

install.packages("stargazer")
library(stargazer)

install.packages("scales")
library(scales)

library(reshape2)
install.packages("plotly")
library(plotly)
install.packages("randomForest")
library(randomForest)
install.packages("corrplot")
library(corrplot)

Bind_Down<- function(X, Y){
###Defining function of X and Y, where X<<<Y

New_Re_Green_Complete_Y<-  (year(rownames(X)))
New_Re_Green_Complete_M<- month(rownames(X))

New_Re_Green_Complete_dates<- data.frame(cbind(New_Re_Green_Complete_M, New_Re_Green_Complete_Y))
colnames(New_Re_Green_Complete_dates)<- c("M" , "Y")

New_Re_Y<- (year(rownames(Y)))
New_Re_M<- month(rownames(Y))

New_Re_dates<- data.frame(cbind(New_Re_M, New_Re_Y))
colnames(New_Re_dates)<- c("M" , "Y")

New_Re_SameD<- inner_join(New_Re_dates, New_Re_Green_Complete_dates)

 if (nrow(New_Re_SameD)!=length(New_Re_dates)){
cat("The Green and Conventional Matrixes were not the same size, Conv was ",(nrow(New_Re_Green_Complete_dates)-nrow(New_Re_dates)), "more than green, so matched dates extracted")
}

Y$Date<- rownames(Y)
Comp_Y<- data.frame(matrix(, nrow=nrow(New_Re_SameD), ncol= ncol(Y)))
Comp_X<- data.frame(matrix(, nrow=nrow(New_Re_SameD), ncol= ncol(X)))

 for (i in 1:nrow(New_Re_SameD)){
Comp_Y[i,]<- subset(Y, ( (month(rownames(Y)))==New_Re_SameD[i,1] & year(rownames(Y))==New_Re_SameD[i,2]))
}

 for (i in 1:nrow(New_Re_SameD)){
Comp_X[i,]<- subset(X, ( (month(rownames(X)))==New_Re_SameD[i,1] & year(rownames(X))==New_Re_SameD[i,2]))
}

rownames(Comp_Y)<- Comp_Y[, ncol( Comp_Y)]
colnames(Comp_Y)<- colnames(Y)
Comp_Y["Date"]<- NULL

rownames(Comp_X)<- Comp_X[, ncol( Comp_X)]
colnames(Comp_X)<- colnames(X)
Comp_X["Date"]<- NULL

if(nrow(Comp_Y)!=nrow(Comp_X)){
cat("Nope, The Green and Conventional Matrixes are not matched correctly, Conv has ",(nrow(Comp_Y)-nrow(Comp_X)), "more than green, fix it")
}

return(data.frame(cbind(Comp_Y,Comp_X)))

}
##detach("package:openxlsx", unload=TRUE)



## Summarizes data.
## Gives count, mean, standard deviation, standard error of the mean, and confidence interval (default 95%).
##   data: a data frame.
##   measurevar: the name of a column that contains the variable to be summariezed
##   groupvars: a vector containing names of columns that contain grouping variables
##   na.rm: a boolean that indicates whether to ignore NA's
##   conf.interval: the percent range of the confidence interval (default is 95%)
summarySE <- function(data, measurevar, groupvars, na.rm=FALSE,
                      conf.interval=.95, .drop=TRUE) {
    library(plyr)

    # New version of length which can handle NA's: if na.rm==T, don't count them
    length2 <- function (x, na.rm=FALSE) {
        if (na.rm) sum(!is.na(x))
        else       length(x)
    }

    # This does the summary. For each group's data frame, return a vector with
    # N, mean, and sd
    datac <- ddply(data, groupvars, .drop=.drop,
      .fun = function(xx, col) {
        c(N    = length2(xx[[col]], na.rm=na.rm),
          mean = mean   (xx[[col]], na.rm=na.rm),
          sd   = sd     (xx[[col]], na.rm=na.rm)
        )
      },
      measurevar
    )

    # Rename the "mean" column    
    datac <- plyr::rename(x=datac, c("mean" = measurevar))

    datac$se <- datac$sd / sqrt(datac$N)  # Calculate standard error of the mean

    # Confidence interval multiplier for standard error
    # Calculate t-statistic for confidence interval: 
    # e.g., if conf.interval is .95, use .975 (above/below), and use df=N-1
    ciMult <- qt(conf.interval/2 + .5, datac$N-1)
    datac$ci <- datac$se * ciMult

    return(datac)
}

## Norms the data within specified groups in a data frame; it normalizes each
## subject (identified by idvar) so that they have the same mean, within each group
## specified by betweenvars.
##   data: a data frame.
##   idvar: the name of a column that identifies each subject (or matched subjects)
##   measurevar: the name of a column that contains the variable to be summariezed
##   betweenvars: a vector containing names of columns that are between-subjects variables
##   na.rm: a boolean that indicates whether to ignore NA's
normDataWithin <- function(data=NULL, idvar, measurevar, betweenvars=NULL,
                           na.rm=FALSE, .drop=TRUE) {
    library(plyr)

    # Measure var on left, idvar + between vars on right of formula.
    data.subjMean <- ddply(data, c(idvar, betweenvars), .drop=.drop,
     .fun = function(xx, col, na.rm) {
        c(subjMean = mean(xx[,col], na.rm=na.rm))
      },
      measurevar,
      na.rm
    )

    # Put the subject means with original data
    data <- merge(data, data.subjMean)

    # Get the normalized data in a new column
    measureNormedVar <- paste(measurevar, "_norm", sep="")
    data[,measureNormedVar] <- data[,measurevar] - data[,"subjMean"] +
                               mean(data[,measurevar], na.rm=na.rm)

    # Remove this subject mean column
    data$subjMean <- NULL

    return(data)
}

# Multiple plot function
#
# ggplot objects can be passed in ..., or to plotlist (as a list of ggplot objects)
# - cols:   Number of columns in layout
# - layout: A matrix specifying the layout. If present, 'cols' is ignored.
#
# If the layout is something like matrix(c(1,2,3,3), nrow=2, byrow=TRUE),
# then plot 1 will go in the upper left, 2 will go in the upper right, and
# 3 will go all the way across the bottom.
#
multiplot <- function(..., plotlist=NULL, file, cols=1, layout=NULL) {
  library(grid)

  # Make a list from the ... arguments and plotlist
  plots <- c(list(...), plotlist)

  numPlots = length(plots)

  # If layout is NULL, then use 'cols' to determine layout
  if (is.null(layout)) {
    # Make the panel
    # ncol: Number of columns of plots
    # nrow: Number of rows needed, calculated from # of cols
    layout <- matrix(seq(1, cols * ceiling(numPlots/cols)),
                    ncol = cols, nrow = ceiling(numPlots/cols))
  }

 if (numPlots==1) {
    print(plots[[1]])

  } else {
    # Set up the page
    grid.newpage()
    pushViewport(viewport(layout = grid.layout(nrow(layout), ncol(layout))))

    # Make each plot, in the correct location
    for (i in 1:numPlots) {
      # Get the i,j matrix positions of the regions that contain this subplot
      matchidx <- as.data.frame(which(layout == i, arr.ind = TRUE))

      print(plots[[i]], vp = viewport(layout.pos.row = matchidx$row,
                                      layout.pos.col = matchidx$col))
    }
  }
}



#####################################################################################

summarySEwithin <- function(data=NULL, measurevar, betweenvars=NULL, withinvars=NULL,
                            idvar=NULL, na.rm=FALSE, conf.interval=.95, .drop=TRUE) {

  # Ensure that the betweenvars and withinvars are factors
  factorvars <- vapply(data[, c(betweenvars, withinvars), drop=FALSE],
    FUN=is.factor, FUN.VALUE=logical(1))

  if (!all(factorvars)) {
    nonfactorvars <- names(factorvars)[!factorvars]
    message("Automatically converting the following non-factors to factors: ",
            paste(nonfactorvars, collapse = ", "))
    data[nonfactorvars] <- lapply(data[nonfactorvars], factor)
  }

  # Get the means from the un-normed data
  datac <- summarySE(data, measurevar, groupvars=c(betweenvars, withinvars),
                     na.rm=na.rm, conf.interval=conf.interval, .drop=.drop)

  # Drop all the unused columns (these will be calculated with normed data)
  datac$sd <- NULL
  datac$se <- NULL
  datac$ci <- NULL

  # Norm each subject's data
  ndata <- normDataWithin(data, idvar, measurevar, betweenvars, na.rm, .drop=.drop)

  # This is the name of the new column
  measurevar_n <- paste(measurevar, "_norm", sep="")

  # Collapse the normed data - now we can treat between and within vars the same
  ndatac <- summarySE(ndata, measurevar_n, groupvars=c(betweenvars, withinvars),
                      na.rm=na.rm, conf.interval=conf.interval, .drop=.drop)

  # Apply correction from Morey (2008) to the standard error and confidence interval
  #  Get the product of the number of conditions of within-S variables
  nWithinGroups    <- prod(vapply(ndatac[,withinvars, drop=FALSE], FUN=nlevels,
                           FUN.VALUE=numeric(1)))
  correctionFactor <- sqrt( nWithinGroups / (nWithinGroups-1) )

  # Apply the correction factor
  ndatac$sd <- ndatac$sd * correctionFactor
  ndatac$se <- ndatac$se * correctionFactor
  ndatac$ci <- ndatac$ci * correctionFactor

  # Combine the un-normed means with the normed results
  merge(datac, ndatac)
}


######################################################
##############functions working#######################
######################################################
##setwd("C:\\Program Files\\R\\R-3.4.1")

##Re_DS_con1<- read.xlsx("Gorandata.xlsx", sheetName ="Sheet1")
Re_DS_con2<- read.xlsx("Gorandata1.xlsx", sheetName ="Sheet1")
Re_DS_con2<- data.frame(Re_DS_con2)

g_7_4<- read.xlsx("7-4.xlsx", sheetName ="7-4(2)")
g_8_6<- read.xlsx("8-6.xlsx", sheetName ="Sheet1")

Re_DS_con2<- data.frame(Re_DS_con2)


colnames(Re_DS_con2)
###(Re_DS_con2)[,5]

colnames(Re_DS_con2)<- c("index", "Date", "Ctime", "time","Glucose")
Re_DS_con2['Ctime'] <- as.POSIXct(Re_DS_con2['Ctime'][,1], format="%H:%M:%S", tz="GMT")
Original<- Re_DS_con2['Ctime']
strptime(c(Original), "%H:%M:%S", tz="GMT")
Re_DS_con2['Ctime'] <- NULL
Re_DS_con2['POS']<- as.POSIXct(Re_DS_con2['time'][,1])
All_d<- data.frame(Re_DS_con2)

##z2 <- as.POSIXct(All_d['time'][,1], "%Y-%m-%d %H:%M:%S", tz="GMT")
##plot(density(as.numeric(z2)))

#df<- data.frame(All_d)

#df$tcol<- z2
#library(ggplot2)
#measurements <- geom_point(aes(x=tcol, y=0), shape=15, color='blue', size=5)
#kde <- geom_density(aes(x=tcol), bw="nrd0")
#ggplot(df) + measurements +  kde




##(Re_DS_con2[,3])

###(as.POSIXct(Re_DS_con2['time'][,1]))

t <- strftime(as.POSIXct(Re_DS_con2['time'][,1]), format="%H:%M:%S", tz="GMT" )
Re_DS_con2['time']<- t

colnames(Re_DS_con2)<- c("index", "Date", "time", "Glucose", "POS")
Re_DS_con2$Date<- as.Date(Re_DS_con2$Date)

DayD<- split(Re_DS_con2, Re_DS_con2$Date, drop=true)
Y <- lapply(seq_along(DayD), function(x) as.data.frame(DayD[[x]])) 

##Lz <- lapply(Y, read.zoo)
##Z_D<- read.zoo(Re_DS_con2)

##Z_date<- Re_DS_con2$Date
##x2 <- aggregate(Z_D, Z_date, mean); Z_D


##unlist(Lz)
#
##install.packages("zoocat")
##library("zoocat")

# This is the air quality example from package reshape2
#Y_zc<- Y[[1]]
#names(Y_zc) <- tolower(names(Y_zc))
#aqm <- melt(Y_zc, id = c("date", "time"), na.rm=TRUE)
#zc <- cast2zoocat(aqm, index.var = 'time', value.var = 'value', fun.aggregate = mean)
#aggregate_col(zc, by = 'variable', FUN = max)
#aggregate_col(zc, by = 'variable', FUN = max, na.rm = TRUE)



Y_cl<- list()
Y_cl<- lapply(1:length(Y), function(i) na.omit(data.frame(Y[[i]])) )

 for (i in 1:length(Y)){
assign(paste0("Date_",(Y[[i]]["Date"][2,])), data.frame((Y[[i]])))
}

#for (i in 1:length(Y_cl)){
#df<- Y_cl[[i]]
#df$time <- as.POSIXct(strptime(df$time, format="%H:%M:%S"))
#Y_cl[[i]]<- df}



###=======================================Getting Data=============



install.packages("Hmisc")
install.packages("rowr")
library(Hmisc)
library(rowr)
D_a1c <- data.frame(sasxport.get("C:/Program Files/R/R-3.4.2/GHB_H.XPT"))
D_PFG <- data.frame(sasxport.get("C:/Program Files/R/R-3.4.2/GLU_H.XPT"))
D_INS <- data.frame(sasxport.get("C:/Program Files/R/R-3.4.2/INS_H.XPT"))
D_OGTT <- data.frame(sasxport.get("C:/Program Files/R/R-3.4.2/OGTT_H.XPT"))

D_BMX <- data.frame(sasxport.get("C:/Program Files/R/R-3.4.2/BMX_H.XPT"))
D_DEM <- data.frame(sasxport.get("C:/Program Files/R/R-3.4.2/DEMO_H.XPT"))


mydocN <- docx( )

mydocN<- addParagraph(mydocN, value= "All data is gathered from the NHANES 2013-2014 Database. The 
official website provides guidelines regarding each variables, under Analytical Notes. Per these notes, each of the variables 
are examined and explained, starting with A1c values, under GHB_H.XPT. All
data files afe inputed from a SAS database provided via the CDC. The first column of all files, seqn refers to unique
patient identifier."  , stylename = "Normal")






mydocN<- addTitle( mydocN, value=paste("SAS metrics for HbA1C inputs"))

Tab1<- as.matrix(head(D_a1c)) 
Tab_1 <- capture.output(print(Tab1))
mydocN<- addFlexTable(  mydocN,
              (FlexTable( Tab1, header.cell.props = cellProperties( background.color =  "#003366" ),
                        header.text.props = textProperties( color = "white", font.size = 7, font.weight = "bold" ),
                         body.text.props = textProperties( font.size = 5 ),
                         add.rownames = TRUE ) %>%
                         setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))



#mydocN<- addParagraph( mydocN, value=Tab_1, stylename = "Normal" )# %>%
mydocN<- addParagraph( mydocN, value="As can be seen the A1c value is denoted as lbxgh
and will remain the same throughout the analysis", stylename = "Normal" )# %>%


mydocN<- addTitle( mydocN, value=paste("SAS file for Fasting Plasma Glucose inputs"))

Tab2<-  as.matrix(head(D_PFG)) 
Tab_2 <- capture.output(print(Tab2))
##mydocN<- addParagraph( mydocN, value=Tab_2, stylename = "Normal" )# %>%

mydocN<- addFlexTable(  mydocN,
              (FlexTable( Tab2, header.cell.props = cellProperties( background.color =  "#003366" ),
                        header.text.props = textProperties( color = "white", font.size = 7, font.weight = "bold" ),
                         body.text.props = textProperties( font.size = 5 ),
                         add.rownames = TRUE ) %>%
                         setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


mydocN<- addTitle( mydocN, value=paste("SAS metrics for Fasting Plasma Glucose"))


mydocN<- addParagraph( mydocN, value=paste ("The details for the variables associated with the Plasma
fasting glucose are available in 2013-2014 Data Documentation, Codebook, and Frequencies
Plasma Fasting Glucose (GLU_H), Data File: GLU_H.xpt. The first variable, wtsaf2yr, denotes the
sampling weight, and per the CDC: There will be two weight files associated with the subsample for the diabetes data. 
Use the fasting sample weights (WTSFA2YR) when analyzing the fasting glucose and insulin levels only. Use the 
OGTT sample weights (WTSOG2YR) when analyzing the insulin, fasting AND OGTT glucose levels or
 when analyzing ONLY OGTT glucose levels. If no lab results existed, the variable is set to 0.0. As the Analysis 
here includes OGTT, Glucose, and insulin levels, the sample weights associated with the OGTT variable will
be used in the analytics. However, the 0.0 in the Fasting Plasma glucose shows whether the Lab results existed 
or were calculated, and as such, all seqn for which the wtsaf2yr is 0 (such as seqn 73574), is deleted from the file. 
This is due to the fact that sampling weights have an important influence in training neural networks (Ref Tianxiang Gao, Vladimir Jojic
) and as such, approximated data with 0 sampling weight is avoided to reduce errors. The two variables lbxglu
and lbdglusi both refer to Glucose levels, responding to mg/dL and mmoL/L respectivley. The lbdglusi is used
in this analysis to allow testing the model on CGM devices with the same unit in the future. It must be
noted that using both to train the NN would not only be redundant, but would cause linear dependency within the 
variables and create an ill conditioned problem. The two variables phasthr and phatsthmn refer to the hours and minutes
of fasting respectivley. "), stylename = "Normal" )# %>%

D_PFG<- subset(D_PFG, D_PFG$wtsaf2yr != 0.0) 
 


D_PFG$lbxglu<- NULL
D_PFG$wtsaf2yr<- NULL

###########mydocN<- addTitle( mydocN, value=paste("SAS file for Insulin inputs"))

Tab3<- (( as.matrix(head(D_INS)) ))
Tab_3 <- capture.output(print(Tab3))
mydocN<- addTitle( mydocN, value=paste("SAS metrics for insulin inputs"))
##mydocN<- addParagraph( mydocN, value=Tab_3, stylename = "DocDefaults" )# %>%

mydocN<- addFlexTable(  mydocN,
              (FlexTable( Tab3, header.cell.props = cellProperties( background.color =  "#003366" ),
                        header.text.props = textProperties( color = "white", font.size = 7, font.weight = "bold" ),
                         body.text.props = textProperties( font.size = 5 ),
                         add.rownames = TRUE ) %>%
                         setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

mydocN<- addParagraph( mydocN, value=paste("As for the fasting plasma glucose, the metrics in the 
insulin include a sample weighting, which as per the NHANES 2013-2014 analytical guidelines, is to discarded infavor
of the sampling weight of the OGTT for cases were both insulin, fasting plasma glucose and OGTT are used in the same
data set. As in the case of the Plasma Fasting Glucose samples with weights of 0.0 attributed to a lack of lab results
will be discarded, and the variable wtsaf2yr discarded from the data set. The insulin value in µU/mL (LBXIN) was converted to pmol/L (LBDINSI) 
by multiplying by 6.0, and LBXIN is used here, taken from the same blood sample the Fasting Plasma Glucose was 
measured. The last two variables phasthr and phafstmn are the same as the above, and have the same value within
Fasting Plasma Glucose and Insulin files for each seqn number."), stylename = "Normal" )# %>%


D_INS<- subset(D_INS, D_INS$wtsaf2yr != 0.0) 
D_INS$wtsaf2yr<- NULL
D_INS$lbxin<- NULL
D_INS$phafsthr<- NULL
D_INS$phafstmn<- NULL


#######mydocN<- addTitle( mydocN, value=paste("SAS file for Oral Glucose Tolerance Test"))

Tab4<- (( as.matrix(head(D_OGTT)) ))
Tab_4 <- capture.output(print(Tab4))
mydocN<- addTitle( mydocN, value=paste("SAS metrics for Oral Glucose Tolerance Test"))
###mydocN<- addParagraph( mydocN, value=Tab_4, stylename = "Normal" )# %>%

mydocN<- addFlexTable(  mydocN,
              (FlexTable( Tab4, header.cell.props = cellProperties( background.color =  "#003366" ),
                        header.text.props = textProperties( color = "white", font.size = 7, font.weight = "bold" ),
                         body.text.props = textProperties( font.size = 5 ),
                         add.rownames = TRUE ) %>%
                         setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

mydocN<- addParagraph( mydocN, value=paste ("The two-hour (OGTT), glucose value in mg/dL (LBXGLT) was converted to 
mmol/L (LBDGLTSI) by multiplying by 0.05551 (rounded to 3 decimals). To be compatible to the Fasting Plasma Glucose
readings, the LBXGLT is used and LBDGLTSI is discarded. As the wtsog2yr is used as sampling weights (per guidelines)
it is not excluded, but all rows with a wtsog2yr of 0, and a LBXGLT of NA is discarded. The remaning metrics are
defined as follows:
GTDSCMMN: used to define Glucose challenge Administer Time in minutes, 
GTDDR1MN: used to define: Time from fast glucose & challenge (min),
GTDBL2MN: used to define: Time from fasting glucose & OGTT (min) ,
GTDDR2MN: used to define: Time from glucose challenge & OGTT (min),
GTXDRANK: used to define:  Amount of glucose challenge the SP drank ,
GTDCODE: used to define:  Incomplete OGTT Comment Code,
The phafsthr and phafstmn correspond to the previous Plasma Fasting Glucose total fasting hours and minutes and
are discarded, as the gtdcode, as the incomplete OGTT rows includes NA which have already been removed."), stylename = "Normal" )# %>%

D_OGTT<- subset(D_OGTT, D_OGTT$wtsog2yr != 0.0) 
D_OGTT<- subset(D_OGTT, is.na(D_OGTT$lbxglt) == FALSE) 
###D_INS$wtsaf2yr<- NULL
D_OGTT$lbdinsi<- NULL
D_OGTT$lbxglt <- NULL

D_OGTT$phafsthr<- NULL
D_OGTT$phafstmn<- NULL
D_OGTT$gtdcode<- NULL


mydocN<- addTitle( mydocN, value=paste("SAS file for Body Measures"))

Tab5<- (( as.matrix(head(D_BMX)) ))
Tab_5 <- capture.output(print(Tab5))
###mydocN<- addParagraph( mydocN, value=Tab_5, stylename = "Normal" )# %>%
mydocN<- addTitle( mydocN, value=paste("SAS metrics for Body Measures"))


mydocN<- addFlexTable(  mydocN,
              (FlexTable( Tab5, header.cell.props = cellProperties( background.color =  "#003366" ),
                        header.text.props = textProperties( color = "white", font.size = 7, font.weight = "bold" ),
                         body.text.props = textProperties( font.size = 5 ),
                         add.rownames = TRUE ) %>%
                         setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

mydocN<- addParagraph( mydocN, value=paste("The NHANES file on body dimensions includes numerous measures including but
not limited to head circumference, limb length, height, weight, etc. For the purposes of this study, only the
BMXBMI - Body Mass Index (kg/m**2) and waist circumference BMXWAIST - Waist Circumference (cm)are used, 
having correlation with Diabetes in patients (REF). It must be noted that although weight and Obesity have been
known to correlate with Diabetes, for the sake of reducing linear dependence between variables as much as possible,
the weight BMXWT kg has been excluded from the data set, and all rows with any NA values have been removed.
The NA values could be changed to 0 to exclude them from their influence during training, but removing the row was
chosen to preserve minimum pre-conditioning of the data"), stylename = "Normal" )# %>%

D_BMX<- D_BMX[ , c("seqn","bmxbmi","bmxwaist")]
D_BMX<- D_BMX[complete.cases(D_BMX), ]


mydocN<- addParagraph( mydocN, value=paste("Having all the variables selected, they are then merged base on the 
seqn patient number. The merging process involved binding all variables in a dataframe based on the seqn numbers 
common between them all. After binding and selecting the complete cases (those not including NA, The amount of
Glucose drank in the glucose tolerance test was 1 within the whole data sample, resulting in NA values in the
Correlation matrix of variables, and the variable was excluded. To Allow the addition of classification
for comparison, a classifying factor of race was Added from the Demographic Data file, RIDRETH3. Two sets of data sets,
one with, and one without the classifier will be used. 
The head of the final dataframe of 2242 patients is 
shown bellow."), stylename = "Normal" )# %>%
D_DEM<- subset(D_DEM, D_DEM$ridreth3 != 0.0)
D_DEM<- D_DEM[ , c("seqn","ridreth3")]

####intersect(colnames(mat1),colnames(mat2))
##head(D_BPX)

D_OGTT$gtxdrank <- NULL
All_D1<-  list(D_a1c,D_PFG, D_INS, D_OGTT, D_BMX)
All_D<- list(D_a1c,D_PFG, D_INS, D_OGTT, D_BMX, D_DEM)

merge.all <- function(x, y) {
    merge(x, y, all=TRUE, by="seqn")
}

output <- Reduce(merge.all, All_D)
output_uc<-  Reduce(merge.all, All_D1)

duplicated(output$seqn)
Clean_D<- as.data.frame(subset(output, !is.na(lbxgh)))
Clean_D<- as.data.frame(subset(output, !is.na(lbdglusi )))

Clean_D_uc<- as.data.frame(subset(output_uc, !is.na(lbxgh)))
Clean_D_uc<- as.data.frame(subset(output_uc, !is.na(lbdglusi )))

f_dat<- Clean_D[complete.cases(Clean_D), ]

colnames(output)
head(f_dat)
Tab6<- (( as.matrix(head(f_dat)) ))
Tab_6 <- capture.output(print(f_dat))
#mydocN<- addParagraph( mydocN, value=Tab_6, stylename = "Normal" )# %>%

mydocN<- addFlexTable(  mydocN,
              (FlexTable( Tab6, header.cell.props = cellProperties( background.color =  "#003366" ),
                        header.text.props = textProperties( color = "white", font.size = 7, font.weight = "bold" ),
                         body.text.props = textProperties( font.size = 5 ),
                         add.rownames = TRUE ) %>%
                         setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


###Patients<- output$gtxdrank 
nrow(f_dat)
cor(f_dat)

mydocN<- addTitle( mydocN, value=paste("Correlation Matrix Gradient"))

mydocN<- addParagraph( mydocN, value="A gradient plot of the correlation matrix of the remaning variables is 
shown in the following graph", stylename = "Normal" )# %>%
ggcorr(f_dat)
p333g.pryr %<a-% { plot(ggcorr(f_dat))}
mydocN<- addPlot( mydocN , fun=function() p333g.pryr) 




fit_CD <- princomp(cor(f_dat), cor=TRUE)
summary(fit_CD) # print variance accounted for 
loadings(fit_CD) # pc loadings 
p1_Conv<- plot(fit_CD,type="lines") # scree plot 
mydocN<- addTitle( mydocN, value=paste("Principal Component Analysis"), level = 1 ) 
 

fit_CD$scores # the principal components
p2_Conv<- biplot(fit_CD)

##############################
Conv_pca <- prcomp(f_dat , scale = TRUE)


T1<- (summary(Conv_pca))
mydocN<- addTitle( mydocN, value=paste("Conventional PCA, Summary" ), level = 2 ) 
mydocN<- addFlexTable(  mydocN,
              (FlexTable( data.frame(round(T1$importance,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

p3bA.pryr %<a-% { biplot(Conv_pca, scale.=0)}

mydocN<- addTitle( mydocN, value=paste("PCA Analysis: Outlying/ Main Affecting Seqn Identification" ), level = 2 ) 
mydocN<- addPlot( mydocN , fun=function() p3bA.pryr) 

################################################################################


#decathlon2.active<- DF[1:(nrow(DF)-0.2*(nrow(DF))), 4:6]
res.pca <- Conv_pca

names(res.pca)
head(res.pca$sdev)
head(unclass(res.pca$rotation))


# Eigenvalues
eig <- (res.pca$sdev)^2
# Variances in percentage
variance <- eig*100/sum(eig)
# Cumulative variances
cumvar <- cumsum(variance)
eig.decathlon2.active <- data.frame(eig = eig, variance = variance,
                     cumvariance = cumvar)
head(eig.decathlon2.active)

summary(res.pca)


eig.val <- get_eigenvalue(res.pca)
head(eig.val)

v_GR<- barplot(eig.decathlon2.active[, 2], names.arg=1:nrow(eig.decathlon2.active), 
       main = "Variances",
       xlab = "Principal Components",
       ylab = "Percentage of variances",
       col ="steelblue")
# Add connected line segments to the plot
lines(x = 1:nrow(eig.decathlon2.active), 
      eig.decathlon2.active[, 2], 
      type="b", pch=19, col = "red")


fv_scr_Conv<- fviz_screeplot(res.pca, ncp=10)

mydocN<- addTitle( mydocN, value=paste("Metric PCA, Scree Plot" ), level = 2 ) 
mydocN<- addPlot( mydocN , fun=print, x=fv_scr_Conv) 

fviz_screeplot(res.pca, ncp=10, choice="eigenvalue")

var_conv <- get_pca_var(res.pca)

Contrb_Conv<- var_conv$contrib

cor_Conv<- var_conv$cor

coord_Conv<- var_conv$coord

Cos2_Conv<- var_conv$Cos2


# Helper function : 
# Correlation between variables and principal components
var_cor_func <- function(var.loadings, comp.sdev){
  var.loadings*comp.sdev
  }
# Variable correlation/coordinates
loadings <- res.pca$rotation
sdev <- res.pca$sdev
var.coord <- var.cor <- t(apply(loadings, 1, var_cor_func, sdev))
head(var.coord)

# Plot the correlation circle
a <- seq(0, 2*pi, length = 100)
plot( cos(a), sin(a), type = 'l', col="gray",
      xlab = "PC1",  ylab = "PC2")
abline(h = 0, v = 0, lty = 2)
# Add active variables
arrows(0, 0, var.coord[, 1], var.coord[, 2], 
      length = 0.1, angle = 15, code = 2)
# Add labels
text(var.coord, labels=rownames(var.coord), cex = 1, adj=1)
fviz_pca_var(res.pca)



pca_conv<- fviz_pca_var(res.pca, col.var="contrib")+
scale_color_gradient2(low="blue",  mid="yellow", 
      high="red", midpoint=55) + theme_minimal()

mydocN<- addTitle( mydocN, value=paste("Metric PCA, Biplot" ), level = 2 ) 
mydocN<- addPlot( mydocN , fun=print, x=pca_conv) 
##########################################Train-1###################################
index <- sample(1:nrow(f_dat),round(0.75*nrow(f_dat)))
train_DF <- f_dat[index,]
train_DF$seqn <- as.factor(train_DF$seqn)
test_DF <- f_dat[-index,]

train_DF$classe <- as.factor(train_DF$ridreth3)
# perform near-zero variance analysis on numeric columns
zero_var_variables <- nearZeroVar(train_DF[sapply(train_DF, is.numeric)], saveMetrics = TRUE)

# rather than display all the results, this will display only variables that have zero or near-zero variance
filter(zero_var_variables, zeroVar == TRUE | nzv == TRUE)


set.seed(3030)

# split dataframe into training, validation & testing dataframes
# 50% of total data goes towards training and 50% of the remaining (25% of total)
# goes towards validation and the other 50% of remaining (25% of total) goes towards testing
inTrain <- createDataPartition(y = train_DF$classe, p=0.50, list=FALSE)
training_DF <- train_DF[inTrain, ]


remaining_DF <- train_DF[-inTrain, ]
inVal <- createDataPartition(y = remaining_DF$classe, p=0.50, list=FALSE)
validating_DF <- remaining_DF[inVal, ]
testing_DF <- remaining_DF[-inVal, ]


# calculate correlation on numeric predictor variables
predictor_corr <- round(cor(training_DF[sapply(training_DF, is.numeric)]), 2)

# plot correlation matrix and order the variables using hierarchical cluster analysis
par(ps=5)
corrplot.mixed(predictor_corr, order = "hclust", tl.col="black", diag = "n", tl.pos = "lt", 
               lower = "circle", upper = "number", tl.cex = 1.5, mar=c(1,0,1,0))


mydocN<- addTitle( mydocN, value=paste("Predictor Relationships & Data Compression
" ), level = 2 ) 

mydocN<- addParagraph( mydocN, value="At this point I have 14 predictor variables. To identify 
additional data reduction options I’ll analyze 
the correlations among the numeric predictor variables. The correlation plot below uses a hierarchical 
cluster analysis approach to group the predictor variables. As a result, there exist clusters of
 higher positively correlated (darker blue) variables along the diagonal; showing the 
groupings of negatively correlated (darker red) variables throughout the dataset.", stylename = "Normal" )# %>%

At this point I have 52 predictor variables. To identify additional data reduction options I’ll analyze 
the correlations among the numeric predictor variables. The correlation plot below uses a hierarchical 
cluster analysis approach to group the predictor variables. As a result, you will notice clusters of
 higher positively correlated (darker blue) variables along the diagonal; this will also show the 
groupings of negatively correlated (darker red) variables throughout the dataset. This plot reveals 
that several groupings of variables with high correlations exist and that principal component analysis
 (PCA) may provide a suitable data reduction technique.

# plot correlation matrix and order the variables using hierarchical cluster analysis
par(ps=5)
corrplot.mixed(predictor_corr, order = "hclust", tl.col="black", diag = "n", tl.pos = "lt", 
               lower = "circle", upper = "number", tl.cex = 1.5, mar=c(1,0,1,0))



p3bB.pryr %<a-% { corrplot.mixed(predictor_corr, order = "hclust", tl.col="black", diag = "n", tl.pos = "lt", 
               lower = "circle", upper = "number", tl.cex = 1.5, mar=c(1,0,1,0))}

mydocN<- addTitle( mydocN, value=paste("Hierarchial Cluster Analysis" ), level = 2 ) 
mydocN<- addPlot( mydocN , fun=function() p3bB.pryr) 

Dno<- ncol(training_DF)

# train PCA model
compress <- preProcess(training_DF[,-17], method = "pca")
# apply PCA model to training, validation and test sets
training_PCA <- predict(compress, training_DF[,-17])
validating_PCA <- predict(compress, validating_DF[,-17])
testing_PCA <- predict(compress, testing_DF[,-17])

# train random forest predictive model
model_1 <- train(training_DF$classe ~., method = "rf", data = training_PCA, 
                 trControl = trainControl(method = "cv", number = 4), 
                 ntree = 100, importance = TRUE)




##########################################
##########################################
##########################################
##########################################
##########################################
writeDoc(mydocN, file = 'NN1.docx')
browseURL("NN1.docx")
##########################################
##########################################
##########################################
##########################################


nrow(output)

Clean_D[is.na(Clean_D)] <- 0.0

is.nan.data.frame <- function(x)
do.call(cbind, lapply(x, is.nan))

Clean_D[is.nan(Clean_D)] <- 0



str(train_)
Clean_D$bpxsy4  

apply(Clean_D,2,function(x) sum(is.na(Clean_D)))

Clean_D<- Clean_D[, colSums(Clean_D != 0) > 0]
data<- Clean_D

index <- sample(1:nrow(data),round(0.75*nrow(data)))
train <- data[index,]
test <- data[-index,]
lm.fit <- glm(lbxgh~., data=train)


summary(lm.fit)
pr.lm <- predict(lm.fit,test)
MSE.lm <- sum((pr.lm - test$lbxgh)^2)/nrow(test)

####Clean_D[, colSums(Clean_D != 0) > 0]


maxs <- apply(data, 2, max) 
mins <- apply(data, 2, min)

scaled <- as.data.frame(scale(data, center = mins, scale = maxs - mins))

train_ <- as.data.frame(scaled[index,])
test_ <- as.data.frame(scaled[-index,])

install.packages("neuralnet")
library(neuralnet)
n <- names(train_)
f <- as.formula(paste("lbxgh ~", paste(n[!n %in% "lbxgh"], collapse = " + ")))

str(train_)
str(test_)


nn <- neuralnet(f,data=train_,hidden=c(5,3),linear.output=T)
plot(nn)

pr.nn <- compute(nn,test_[,1:13])

####################################################################################
 ##nn <- x
rep<-1
covariate<- test_[,1:13]
    linear.output <- nn$linear.output
    weights <- nn$weights[[rep]]
    nrow.weights <- sapply(weights, nrow)
    ncol.weights <- sapply(weights, ncol)
    weights <- unlist(weights)
    if (any(is.na(weights))) 
        weights[is.na(weights)] <- 0
    weights <- neuralnet:::relist(weights, nrow.weights, ncol.weights)
    length.weights <- length(weights)
    covariate <- as.matrix(cbind(1, covariate))
    act.fct <- nn$act.fct
    neurons <- list(covariate)
    if (length.weights > 1) 
        for (i in 1:(length.weights - 1)) {
            temp <- neurons[[i]] %*% weights[[i]]
            act.temp <- act.fct(temp)
            neurons[[i + 1]] <- cbind(1, act.temp)
        }
    temp <- neurons[[length.weights]] %*% weights[[length.weights]]
    if (linear.output) 
        net.result <- temp
    else net.result <- act.fct(temp)
    list(neurons = neurons, net.result = net.result)
#########################################################################################


compute(nn,test[,2:4])

pr.nn_ <- pr.nn$net.result*(max(data$medv)-min(data$medv))+min(data$medv)
test.r <- (test_$medv)*(max(data$medv)-min(data$medv))+min(data$medv)

MSE.nn <- sum((test.r - pr.nn_)^2)/nrow(test_)


###Clean_Dat<- complete.cases(output)

# character variables are converted to R factors
###================================================================
###================================================================
###================================================================
###================================================================
###================================================================
###================================================================
###================================================================
###================================================================
###================================================================



mydocD <- docx( )



#myplots<- lapply(Y_cl,function(X) {

#g<- ggplot(X,aes( x=(POS),y=Glucose,group=factor(Date),color=factor(Date))) + geom_point()+
#theme(legend.position="bottom")+ 
#scale_x_datetime(breaks = date_breaks("120 min"), labels = date_format("%H:%M:%S"))
#ggMarginal(g, type = "histogram", margins="y", fill="transparent")

#g1<- ggplot(X,aes( x=(POS),y=seq_along(POS),group=factor(Date),color=factor(Date))) + geom_point()+
#theme(legend.position="bottom")+ 
#scale_x_datetime(breaks = date_breaks("120 min"), labels = date_format("%H:%M:%S"))

#pF<- multiplot(g, g1, cols=1)
#return(pF) }

#)




myplots2<- lapply(Y_cl,function(X) ggplot(X,aes( x=seq_along(POS),y=POS,group=factor(Date),color=factor(Date))) + geom_point()+
theme(legend.position="bottom")+ 
scale_y_datetime(breaks = date_breaks("120 min"), labels = date_format("%H:%M:%S")))


mydf<- Y_cl[[1]]
aggregate(. ~ cut(mydf$POS, "5 min"), 
          mydf[setdiff(names(mydf), "POS")], 
          mean)

data<- Y_cl[[1]]
data$run15minavg <- sapply(1:nrow(data), function(i) {
                sum(((data[1:i, c("POS")] >= (data$POS[i] - as.difftime(15, units="mins")))
                      & (data[1:i, c("POS")] <= (data$POS[i]) ))
                      
                   *  data[1:i,]$Glucose) /
                sum((data[1:i, c("POS")] >= (data$POS[i] - as.difftime(15, units="mins")))
                      & (data[1:i, c("POS")] <= (data$POS[i])))
                                     }    
             )



mydocD<- addTitle( mydocD, value=paste("Goran Glucose Level over 10 days, Statistical Study" ), level = 1 )   
mydocD<- addParagraph(mydocD, value= "Initially all NA values are removed and the Glucose Levels
plotted for each day vs time to look at fluctuations.", stylename = "DocDefaults")
##mydocA<- addFlexTable(  mydocA,
              #(FlexTable( as.matrix(colnames(New_Re)), header.cell.props = cellProperties( background.color =  "#003366" ),
                       #    header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                        #   body.text.props = textProperties( font.size = 7 ),
                         #  add.rownames = TRUE ) %>%
                         #  setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

             

for (i in 1:length(Y_cl)){
K<- data.frame()
Nans_p<- (nrow(Y[[i]])-nrow(Y_cl[[i]]))/nrow(Y[[i]])
K<- cbind(nrow(Y[[i]]), nrow(Y_cl[[i]]), percent(Nans_p)) 
rownames(K)<- paste("Data for" , Y_cl[[i]]['Date'][3,1])
colnames(K)<- c("Total Number of Data point", "Number of Measured GL", "% of Na Values in Data")
mydocD<- addTitle(mydocD, value=paste("Day", Y_cl[[i]]['Date'][3,1]), level=2)

addFlexTable(  mydocD,
              (FlexTable( (K), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))





####Kj<- myplots[[i]]
p333.pryr %<a-% { 

#for (i in 1:length(Y_cl)){
X<- Y_cl[[i]]


g<- ggplot(X,aes( x=(POS),y=Glucose,group=factor(Date),color=factor(Date))) + geom_point()+
theme(legend.position="bottom")+ 
scale_x_datetime(breaks = date_breaks("120 min"), labels = date_format("%H:%M:%S"))
 ##ggMarginal(g, type = "histogram", margins="y", fill="transparent") ####}

###p3332.pryr %<a-% { 

###for (i in 1:length(Y_cl)){
###X<- Y_cl[[i]]


g1<- ggplot(X,aes( x=(POS),y=seq_along(POS),group=factor(Date),color=factor(Date))) + geom_point()+
theme(legend.position="bottom")+ 
scale_x_datetime(breaks = date_breaks("120 min"), labels = date_format("%H:%M:%S"))+ 
 geom_histogram(aes(y = ..density..), bins=10)

GL<- X$Glucose
D_g<- diff(GL)
t_d<- data.frame(as.POSIXct(X$POS))

Dff_G<- data.frame(cbind(data.frame(t_d[2:length(t_d),1]), D_g))
gD<- ggplot(Dff_G, aes(x=Dff_G[,1], y=Dff_G[,2]))+geom_point()+
theme(legend.position="bottom")+ 
scale_x_datetime(breaks = date_breaks("120 min"), labels = date_format("%H:%M:%S"))

multiplot(g, g1, cols=1) 
###ggMarginal(g1 , type = "histogram", margins="y", fill="transparent")
##multiplot( ggMarginal(g, type = "histogram", margins="y", fill="transparent") ####}
##, ggMarginal(g1 , type = "histogram", margins="y", fill="transparent")
##, cols=1) 
}

mydocD<- addPlot( mydocD , fun=function() p333.pryr ) 
###mydocD<- addPlot( mydocD , fun=function() p3332.pryr ) 


#k1<- multiplot(g, g1, cols=2) 


#########mydocD<- addPlot( mydocD , fun=print, x=k1) 
#mydocD<- addPlot( mydocD , fun=function() multiplot(g, g1, cols=1) ) 

#######}
####mydocD<- addPlot( mydocD , fun=function() p333.pryr) 

##Kj1<- myplots2[[i]]
##p3331.pryr %<a-% { plot(Kj1)}
##mydocD<- addPlot( mydocD , fun=function() p3331.pryr) 


Dens<- data.frame
Dens<- data.frame(Y[[i]])

##density(Dens$time)
##as.time(Dens$time)

###dtPOSIXct <- as.POSIXct(All_d$X0)
##strptime(Dens$time,"%H:%M:%S")

# extract time of 'date+time' (POSIXct) in hours as numeric
dtTime <-strptime(Dens$time,"%H:%M:%S") ####as.numeric(dtPOSIXct - trunc(dtPOSIXct, "days"))
nrow(Dens)
length(dtTime)
pA.pryr %<a-% {par(mfrow=c(1,2))
Hour <- dtTime$hour
histG<- hist(Dens$Glucose,  main="Glucose")
histH<- hist(Hour, breaks=seq(0, 23), main="Start time (hour)")}
mydocD<- addParagraph(mydocD, value= "Ideally the NA values should not exist but the high sampling frequecy reserved, as such, 
the density plots are drawn and compared for Glucose and hours of measurements. Should these not be normal, a method of normalization
must then be applied.")
mydocD<- addPlot( mydocD , fun=function() pA.pryr) 

Dens$Hour<- dtTime$hour
Dens$post<- as.POSIXct(dtTime)
###p <- qplot(dtTime) + xlab("Time slot") + scale_x_datetime(format = "%S:00")
###print(p)

mtlong <- reshape2::melt(Dens) ## id="Date","time")
P_Dens<- ggplot(mtlong, aes(value)) + facet_wrap(~variable, scales = 'free_x') +
  geom_density()

mydocD<- addPlot( mydocD , fun=print, x=P_Dens) 


Tab1<- (PP.test(as.matrix(Y_cl[[i]]["Glucose"])))
Tab2<-( kpss.test(as.matrix(Y_cl[[i]]["Glucose"])))
Tab3<- adf.test(as.matrix(Y_cl[[i]]["Glucose"]))

Tab_all <- capture.output(print(Tab1), print(Tab2), print(Tab3))
##Tab4<- rbind(Tab1, Tab2, Tab3)

mydocD<- addTitle( mydocD, value=paste("Testing Stationarity for Glucose on Date", Y_cl[[i]][2,2]), level = 1 )
mydocD<- addParagraph( mydocD, value=Tab_all, stylename = "DocDefaults" )# %>%

#strptime(dtTime,"%H:%M:%S")
#Dens_d<- as.data.table(Dens)
#Dens_dt<- na.omit(Dens_d)
#Dens_Av<- Dens_dt[, c('Hour', 'Minute') := .(data.table::hour(Dens_dt$post), minute(Dens_dt$post))
 #][, .(Avg = mean(value)), .(Hour, Minute)]


} 

mydocD<- addTitle( mydocD, value=paste("Daily Summary of Glucose Levels Based on Medicaton and Food"), level = 1 )
mydocD<- addParagraph( mydocD, value="In order to provide the doctor with a final summary, the possible combinations
of the variables (at this stage food and medication) are counted, and the number of data points corresponding to
each measurement is shown by N, the average glucose level of which is shown under Glucose. 
Sd and Se stand for Standard Deviation and Standard error of the mean, 
respectivley.", stylename = "DocDefaults" )# %>%

###T1<- Y_cl[[21]]['POS']

YPOS<- lapply(Y_cl, '[[', 'POS')


Seif<- function(i){
strftime(YPOS[[i]], format="%H")
K1<- (floor((as.numeric(strftime(YPOS[[i]], format="%M")))/15))*15
K2<- strftime(YPOS[[i]], format="%Y-%m-%d %H", tz="GMT")
TT<- paste0(K2, ':', K1)
T_av<- as.POSIXct(TT,format="%Y-%m-%d %H:%M", tz="GMT" )

K1_5m<- (floor((as.numeric(strftime(YPOS[[i]], format="%M")))/5))*5
K2_5m<- strftime(YPOS[[i]], format="%Y-%m-%d %H", tz="GMT")
TT_5m<- paste0(K2_5m, ':', K1_5m)
T_av_5m<- as.POSIXct(TT_5m,format="%Y-%m-%d %H:%M", tz="GMT" )


##K1_h<- (floor((as.numeric(strftime(YPOS[[i]], format="%M")))/5))*5
K2_h<- strftime(YPOS[[i]], format="%Y-%m-%d %H", tz="GMT")
TT_h<- paste0(K2_h, ':', '00')
T_h<- as.POSIXct(TT_h,format="%Y-%m-%d %H:%M", tz="GMT" )


food<- sample(c("yes","no"), replace=TRUE, size=nrow(Y_cl[[i]]), prob = c(0.25,0.75) )
###food2<- rnorm(n, mean = 0, sd = 1)
Med<- sample(c("Metformin","Insulin", "Amaryl", "Duetact", "No" ), replace=TRUE, size=nrow(Y_cl[[i]]), prob = c(0.05,0.05,0.05,0.05,0.8)  )



Kaf<- cbind(Y_cl[[i]], T_av, T_av_5m, T_h, food, Med)
##return (Kaf)

Test<- Kaf

library("plyr")
SUM_D<- summarySE( data=Test, measurevar="Glucose", groupvars=c("Med","food") )
Tab_sum<- data.frame(summarySE( data=Test, measurevar="Glucose", groupvars=c("Med","food") ))
K_out<- (list(Kaf, Tab_sum))


Tab_all2 <- capture.output(K_out[2])
mydocD<- addTitle( mydocD, value=paste("Summary of Day", Y_cl[[i]][2,2]), level = 2 )

addFlexTable(  mydocD,
              (FlexTable( (Tab_sum), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))





###mydocD<- addParagraph( mydocD, value=Tab_all2, stylename = "DocDefaults" )
return(K_out)

 }


Y_cl3<- lapply(1:length(Y_cl), function(i) Seif(i) )


#####################################################################################################

Karim<- function(i){
tgc<-  summarySE( data=Y_cl3[[i]][[1]], measurevar="Glucose", groupvars=c("Med","food","T_h"), na.rm=FALSE)
tgc[is.na(tgc)] <- 0

Data<- Y_cl3[[i]][[1]]
library(plyr)
G_15m<- ddply(Y_cl3[[i]][[1]],"T_av",numcolwise(mean))
G_5m<- ddply(Y_cl3[[i]][[1]],"T_av_5m",numcolwise(mean))
G_h<- ddply(Y_cl3[[i]][[1]],"T_h",numcolwise(mean))
G_15m$index<- NULL
G_5m$index<- NULL
G_h$index<- NULL

Data$G_15m_av<-G_15m[match(Data$T_av, G_15m$T_av),2]
Data$G_5m_av<-G_5m[match(Data$T_av_5m, G_5m$T_av_5m),2]
Data$G_h_av<-G_h[match(Data$T_h, G_h$T_h),2]


library(ggplot2)
library(reshape2)
d <- melt(Data, id.vars="time")


library(ggplot2)
library(reshape2)
meltdf <- melt(Data,id.vars="POS", measure.vars=c("Glucose", "G_15m_av", "G_5m_av", "G_h_av"))
T_av_P<- ggplot(meltdf,aes(x=POS,y=value,colour=variable,group=variable)) +geom_point()+
scale_x_datetime(breaks = date_breaks("60 min"), labels = date_format("%H:%M:%S"))+ 
xlab("Time of Day") +
    ylab("Glucose") +
ggtitle("Comparison of Sensor Output, with 5m, 15m, and Hourly Averages") + facet_grid(variable ~ .)
               

#T_av_P + facet_grid(variable ~ .)

###ggplotly()


mydocD<- addTitle( mydocD, value=paste("Glucose Levels Based on 
Averaging time-frames of 5,15,30 minutes with Original Values",Y_cl3[[i]][[1]][2,2] ), level = 2 )
mydocD<- addPlot( mydocD , fun=print, x=T_av_P) 


mydocD<- addParagraph(mydocD, value="To show the overall affects of the medication and food on the Glucose levels, the regressional analysis method  
LOESS (locally weighted smoothing)is applied to the Glucose readings throughout the dates.")


####pd <- position_dodge(0.1) 
f1<- ggplot(tgc, aes(x=T_h, y=Glucose, colour=food, group=food)) + 
geom_point(alpha=.3) +
    geom_smooth(span = 0.3, alpha=0.1, size=1)+
xlab("Time of Day (H)") +
    ylab("Glucose") +geom_count()+
ggtitle("The Effect of Food on Hourly Averaged Glucose") 

mydocD<- addPlot( mydocD , fun=print, x=f1) 



#M1<- ggplot(tgc, aes(x=T_h, y=Glucose, colour=Med, group=Med)) + 
   # geom_errorbar(aes(ymin=Glucose-se, ymax=Glucose+se), colour="black", width=.1, position=pd) +
   # geom_line(position=pd) +
#xlab("Time of Day (H)") +
   # ylab("Glucose") + geom_count()+
#ggtitle("The Effect of Medication on Glucose") 
#mydocD<- addPlot( mydocD , fun=print, x=M1) 




M1<- ggplot(tgc, aes(x=T_h, y=Glucose, colour=Med)) +
    geom_point(alpha=.3) +
    geom_smooth(span=.3 ,alpha=0.1, size=1)+
xlab("Time of Day (H)") +
    ylab("Glucose") + geom_count()+
ggtitle("The Effect of Medication on Hourly Averaged Glucose") 
mydocD<- addPlot( mydocD , fun=print, x=M1) 



 
Med1<- ggplot(Data, aes(POS, Glucose)) + geom_line()+ geom_point(data=subset(Data,Med!="No")) + 
geom_text(data=subset(Data,Med!="No"),
            aes(POS,Glucose,label=Med, colour=Med), size=2.5)+
xlab("Time of Day (H)") +
    ylab("Glucose") + 
ggtitle("Trend of Blood Glucose with Each Medication") 
mydocD<- addPlot( mydocD , fun=print, x=Med1) 


food1<- ggplot(Data, aes(POS, Glucose)) + geom_line()+ geom_point(data=subset(Data,food!="no")) + 
geom_text(data=subset(Data,food!="no"),
            aes(POS,Glucose,label=food, colour=food), size=2.5)+
xlab("Time of Day (H)") +
    ylab("Glucose") +
ggtitle("Trend of Blood Glucose with Food") 
mydocD<- addPlot( mydocD , fun=print, x=food1) 


}

Y_cl4<- lapply(1:length(Y_cl3), function(i) Karim(i) )

writeDoc(mydocD, file = 'Diab3.docx')
browseURL("Diab3.docx")
###########################################################################
###########################################################################
#######################        27-12-2017     #############################
###########################################################################
###########################################################################



install.packages("plot3D")
library(plot3D)

## 
## sctt3D> ## =======================================================================
## sctt3D> ## text3D and scatter3D
## sctt3D> ## =======================================================================
## sctt3D> 
 with(Data, text3D(Glucose, food, Med, 
   colvar = UrbanPop, col = gg.col(100), theta = 60, phi = 20,
   xlab = "Med", ylab = "food", zlab = "Glucose", 
     main = "Patient Visual Summary", 
     labels = POS,
               cex = 0.6, 
    bty = "g", ticktype = "detailed", d = 2,
     clab = c("Urban","Pop"), adj = 0.5, font = 2))
## 
## sctt3D>  with(USArrests, scatter3D(Murder, Assault, Rape - 1, 
## sctt3D+     colvar = UrbanPop, col = gg.col(100), 
## sctt3D+     type = "h", pch = ".", add = TRUE))







df <- ldply(Y_cl3[[i]], rbind)





tgc2 <- tgc
tgc2$T_h<- factor(tgc2$T_h)

# Error bars represent standard error of the mean
ggplot(tgc2, aes(x=T_h, y=Glucose, fill=food)) + 
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=Glucose-se, ymax=Glucose+se),
                  width=.2,                    # Width of the error bars
                  position=position_dodge(.9))

dfw<- Y_cl3[[21]][[1]]
dfw$T_h <- factor(dfw$T_h)
library(reshape2)
dfw_long <- melt(dfw,
                 id.vars = "T_h",
                 measure.vars = c("yes","no"),
                 variable.name = "food")









Med_s<- ddply(Test, c("Med", "Glucose"), summarise,
               N    = length(Glucose),
               mean = mean(Glucose),
               sd   = sd(Glucose),
               se   = sd / sqrt(N)
)

Food_s<- ddply(Test, c( "food","Med", "Glucose","T_av_5m"), summarise,
               N    = length(Glucose),
               mean = mean(Glucose),
               sd   = sd(Glucose),
               se   = sd / sqrt(N)
)


ggplot(Food_s, aes(x=dose, y=len, colour=supp, group=supp)) + 
    geom_errorbar(aes(ymin=len-ci, ymax=len+ci), colour="black", width=.1, position=pd) +
    geom_line(position=pd) +
    geom_point(position=pd, size=3)











Y_P<- lapply(1:length(YPOS), function(i) strftime(YPOS[[i]], format="%H:%M", tz="GMT") )
Y_P2<- lapply(1:length(YPOS), function(i) strptime(Y_cl[[i]]['POS'], format="%H:%M", tz="GMT") )
}




Tt<- Y_P[[1]]
ff <-strptime(Dens$time,"%H:%M:%S") ####as.numeric(dtPOSIXct - trunc(dtPOSIXct, "days"))
nrow(Dens)
length(dtTime)
pA.pryr %<a-% {par(mfrow=c(1,2))
Hour <- dtTime$hour

Tt$Hour

##Y_P2<- lapply(1:length(Y_cl), function(i) strftime(c(Y_cl[[i]]['POS']), format="%H:%M:%S", tz="GMT") )




DP1<- (YPOS[[1]])
ggplot(DP1, aes(x=rownames(DP1), y=DP1[,1])) +geom_point()+scale_x_datetime(breaks = date_breaks("60 min"), labels = date_format("%H:%M:%S"))

 AB <- Y_cl[[1]]
ABB<- AB$POS
seq_along(ABB)

myplots<- lapply(Y_cl,function(X) ggplot(X,aes( x=POS,y=Glucose,group=factor(Date),color=factor(Date))) + geom_point()+
theme(legend.position="bottom")+
scale_x_datetime(breaks = date_breaks("60 min"), labels = date_format("%H:%M:%S")))


myplots2<- lapply(Y_cl,function(X) ggplot(X,aes( x=seq_along(POS),y=POS,group=factor(Date),color=factor(Date))) + geom_point()+
theme(legend.position="bottom")+
scale_y_datetime(breaks = date_breaks("60 min"), labels = date_format("%H:%M:%S")))

Y_cl[[1]] %>%
  group_by(POS = cut(POS, breaks="14 min")) %>%
  summarize(Glucose= mean(Glucose))


trainURL <- "http://d396qusza40orc.cloudfront.net/predmachlearn/pml-training.csv"
train_DF <- read.csv(file=trainURL, na.strings = c("NA", ""), stringsAsFactors=FALSE)


length(Y)
nrow(Y[[3]])

####Yz <- lapply(Y, read.zoo, index = 1:3, format = "%Y %m %d")



Ytime<- lapply(Y_cl, '[[', 'time')
YDate<- lapply(Y_cl, '[[', 'Date')
YDate_N1<- (lapply(YDate, as.Date))

class(YDate_N1[[1]])

YDate_N <- (lapply(YDate_N1, cbind('['), 1))
Dayd<- list()
for (i in 1:length(YDate_N)){
Dayd1<- data.frame(as.Date(YDate_N[[i]][1]))
Dayd[[i]]<- Dayd1
}
 
Dnames<- do.call(rbind.data.frame, Dayd)

#unlist(Dayd,recursive=FALSE)


###unlist(YDate_N, recursive=FALSE)

####as.Date(YDate[[1]])
YDate_N1<- (lapply(YDate, 'data.frame'))

dat<-YDate_N1

dat <- lapply(dat, function(x) cbind(x = seq_along(x), y = x))
names(dat)<- c(Dnames[,1])
list.names <- names(dat)
lns <- sapply(dat, nrow)
dat <- as.data.frame(do.call("rbind", dat))
dat$group <- rep(list.names, lns)

library(ggplot2)

ggplot(dat, aes(x = x, y = y, colour = group)) +
    theme_bw() +
    geom_line(linetype = "dotted")




##format(strptime("1970-01-01", "%Y-%m-%d", tz="UTC") + round(as.numeric(your.time)/900)*900,"%H:%M")
##when formatting to only minute, we ended up with alot of replications, as data is taken in many seconds per
##minute. To perform PCA, we will need to learn to apply Zoo objects and check if it is possible to effectivley 
## do a PCA on static/dynamic data. We need to check what time frames actually allows "real time" in the data
## if the n minutes roundup should be decided by clinicians, or the code. 
##round(as.numeric(Ytime)/900)*900


for (i in 1:length(ALl_n_C)){
 for (j in 1:ncol(ALl_n_C[[i]])){
assign(paste0(colnames(ALl_n_C[[i]][j])), as.data.table((ALl_n_C[[i]][j]), keep.rownames=TRUE ))
}}


Reduce(intersect, Ytime)


Yt_all<- unlist(Ytime)
T_df<- unique(Yt_all)

library(zoo)

do.call(rbind, Y[[i]]$Date)
lapply(length(Ytime), function(i) do.call(rbind, Ytime))
c(Y[[i]]["Date"])




Y[[21]]
class(Y)

Y %>%
    Reduce(function(dtf1,dtf2) merge(dtf1["Date"],dtf2["Date"]), .)


A<- c(1,22,3,6,43,61,7,8,9)
BB<- c(2,22,3,3,3,43,12,37,1)
merge(A,BB)

Re_DS_con2["index"]<- NULL
Re_DS_con2$Date<- as.Date(Re_DS_con2[,1])
##rownames(Re_DS_con2)<- Re_DS_con2$Date
d<- ((Re_DS_con2))
nn<-do.call('data.frame', split(d, d$Date))

data.frame(split(d, d$n))


names(nn)[-1]<-as.character(d$cat)

data.frame(Re_DS_con1)
Re_DS_con1[,1]<- NULL
Re_DS_con1[,1]<- NULL
colnames(Re_DS_con1)<- c("rn", "time","stamp",


#Re_DS_Green1<-read.xlsx("New_1.xlsx",sheetName ="DS_GreenEq")
getwd()
###-------------------------
###------Cleaning up sheet 1
###-------------------------

N1<- ncol(Re_DS_con1)
Re_DS_con<- Re_DS_con1[,2:N1 ]
rownames(Re_DS_con)<- as.Date(Re_DS_con1[,1])
colnames(Re_DS_con1)

N<- ncol(Re_DS_con)

###in case later needed to extract all words from column names:
###----MAKE SURE DPLYR IS INSTALLED CORRECTLY, IS BIT MOODY
MK_names<- names(Re_DS_con %>% select(contains("MARKET.VALUE")))
market_value1<- Re_DS_con[names(Re_DS_con %>% select(contains("MARKET.VALUE")))]

New_Re1<-Re_DS_con[ , !(names(Re_DS_con) %in% MK_names)]
head(New_Re1)

New_Re2<- data.frame()
for (i in 2:nrow(New_Re1)){
    for (j in 1:ncol(New_Re1)){
New_Re2[i-1,j]<- (((New_Re1[i,j]-New_Re1[(i-1),j])/New_Re1[(i-1),j]))
}
}
colMeans(New_Re2)
New_RF<- New_Re2[,1]
nrow(New_Re2)
rownames(New_Re2)<- as.Date(rownames(New_Re1[2:nrow(New_Re1),]))
colnames(New_Re2)<- c(colnames(New_Re1[,1:ncol(New_Re1)]))

New_Re2<- New_Re2[,2:ncol(New_Re2)]

#New_Re<- data.frame(New_Re2[,2],New_Re2[,5],New_Re2[,6],New_Re2[,11])
New_Re<- New_Re2[complete.cases(data.frame(New_Re2)),]
#rownames(New_Re)<- as.Date(rownames(New_Re2))
#colnames(New_Re)<- c(colnames(New_Re2)[2], colnames(New_Re2)[5], colnames(New_Re2)[6], colnames(New_Re2)[11])
colnames(New_Re)<- c(colnames(New_Re2))

market_value<- data.frame()
###selecting columns we want
##market_value1<- cbind(market_value1[,1],market_value1[,2],market_value1[,3],market_value1[,5])
market_value<- data.frame(market_value1[-1,1],market_value1[-1,2],market_value1[-1,3],market_value1[-1,5])
colnames(market_value)<- c(colnames(market_value1)[1], colnames(market_value1)[2], colnames(market_value1)[3], colnames(market_value1)[5])
rownames(market_value)<- as.Date(rownames(market_value1[-1,]))

head(market_value1)
head(market_value)

###----getting shortenned names 

R_names<- list()
Data_D<- list()
N<- ncol(market_value)
for (i in 1:N){

R_names=  (paste(sapply(strsplit(as.character(colnames(market_value)[i]),"\\."), `[`, 1:3), collapse= " "))

Data_D[[i]]<- R_names
All_dat<- do.call(rbind,Data_D)
}
colnames(market_value)<- All_dat

R_names5<- list()
Data_D5<- list()
N5<- ncol(New_Re)
for (i in 1:N5){

R_names5=  (paste(sapply(strsplit(as.character(colnames(New_Re)[i]),"\\."), `[`, 1:3), collapse= " "))

Data_D5[[i]]<- R_names5
All_dat5<- do.call(rbind,Data_D5)
}
colnames(New_Re)<- NULL
colnames(New_Re)<- All_dat5

head(New_Re)
###----DOCUMENT 

mydocA <- docx( )

mydocA<- addTitle( mydocA, value=paste("All Conventional and Green indices, Statistical Study" ), level = 1 )   
mydocA<- addParagraph(mydocA, value= "As discussed, the selected data to study are listed bellow, along with abreviated names, and returns calculated annually from total returns listed in Excel Sheet", stylename = "DocDefaults")
mydocA<- addFlexTable(  mydocA,
              (FlexTable( as.matrix(colnames(New_Re)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

             


###----Getting Density Plots for CONVENTIONAL	

New_Re<- data.frame(New_Re)
mtlong <- reshape2::melt(New_Re)

P_New_Hist<- ggplot(mtlong, aes(value)) + facet_wrap(~variable, scales = 'free_x') +
  geom_density()
geom_histogram(binwidth = function(x) 2 * IQR(x) / (length(x)^(1/3)))

mydocA<- addTitle( mydocA, value=paste("Density Plots of Conventional Data Used" ), level = 1 )   
mydocA<- addPlot( mydocA , fun=print, x=P_New_Hist)   
#mydocA<- addPlot( mydocA , fun=print, x=ggplot(New_Re))   

#writeDoc(mydocA, file = 'Testing.docx')
#browseURL("Testing.docx")

###-------------------------
###------Cleaning up sheet 2
###-------------------------

N1<- ncol(Re_DS_Green1)
Re_DS_Green2<- Re_DS_Green1[,2:N1 ]
rownames(Re_DS_Green2)<- as.Date(Re_DS_Green1[[1]])

N<- ncol(Re_DS_Green2)

###in case later needed to extract all words from column names:

MK_names_DS_GRN<- names(Re_DS_Green2 %>% select(contains("MARKET.VALUE")))
market_value_DS_GRN<- Re_DS_Green2[names(Re_DS_Green2 %>% select(contains("MARKET.VALUE")))]

head(market_value_DS_GRN)

New_Re_DS_GRN1<- data.frame()

New_Re_DS_GRN1<-(Re_DS_Green2[ , !(names(Re_DS_Green2) %in% MK_names_DS_GRN)])
New_Re_DS_GRN <- data.frame()


for (i in 2:nrow(New_Re_DS_GRN1)){
    for (j in 1:ncol(New_Re_DS_GRN1))
New_Re_DS_GRN[i-1,j]<- (((New_Re_DS_GRN1[i,j]-New_Re_DS_GRN1[(i-1),j])/New_Re_DS_GRN1[(i-1),j]))
}

colnames(New_Re_DS_GRN)<- colnames(New_Re_DS_GRN1)

rownames(New_Re_DS_GRN)<- as.Date(rownames(Re_DS_Green2[-1,]))

New_Re_DS_GRN<- New_Re_DS_GRN[,1:5]

##-----08-10-2017 Dealing with S&P Green data

Re_SP_Green<-data.frame(read.xlsx("New_1.xlsx", sheetName= "Sheet1", detectDate=TRUE))
Re_SP_Green_mv<-data.frame(read.xlsx("New_1.xlsx", sheetName= "Sheet3"))

SP_Gr_I<- Re_SP_Green[,1:2]
SP_CE_TR<- Re_SP_Green[,3:4]
SP_FF_TR<- Re_SP_Green[,7:8]

SP_Gr_I<- SP_Gr_I[complete.cases(SP_Gr_I), ]
colnames(SP_Gr_I)<- c("Dates", "GR_I")

SP_CE_TR<- SP_CE_TR[complete.cases(SP_CE_TR), ]
colnames(SP_CE_TR)<- c("Dates", "SP_CE_TR")

SP_FF_TR<- SP_FF_TR[complete.cases(SP_FF_TR), ]
colnames(SP_FF_TR)<- c("Dates", "SP_FF_TR")


Dates<- SP_Gr_I[,1]

D1<- SP_Gr_I %>% 
  group_by(strftime(Dates, "%Y-%m")) %>% #Groups by the yearmonths
  filter(Dates == max(Dates)) %>%        #Take the last date of each group
  .$Dates                              #Returns the filtered dates as a vector

D2<- SP_CE_TR %>% 
  group_by(strftime(Dates, "%Y-%m")) %>% #Groups by the yearmonths
  filter(Dates == max(Dates)) %>%        #Take the last date of each group
  .$Dates                              #Returns the filtered dates as a vector

D3<- SP_FF_TR %>% 
  group_by(strftime(Dates, "%Y-%m")) %>% #Groups by the yearmonths
  filter(Dates == max(Dates)) %>%        #Take the last date of each group
  .$Dates                              #Returns the filtered dates as a vector



SP_Gr_I<- SP_Gr_I[SP_Gr_I$Dates %in% as.Date(D1),]
rownames(SP_Gr_I)<- format( SP_Gr_I$Dates, format="%Y-%m")
SP_Gr_I<- data.frame(SP_Gr_I)
SP1<- SP_Gr_I[,2]
S1<- data.frame(SP1)
rownames(S1) <- format( SP_Gr_I$Dates, format="%Y-%m")


SP_CE_TR<- SP_CE_TR[SP_CE_TR$Dates %in% as.Date(D2),]
rownames(SP_CE_TR)<- format( SP_CE_TR$Dates, format="%Y-%m")
SP_CE_TR<- data.frame(SP_CE_TR)
SP2<- SP_CE_TR[,2]
S2<- data.frame(SP2)
rownames(S2) <- format( SP_CE_TR$Dates, format="%Y-%m")

SP_FF_TR<- SP_FF_TR[SP_FF_TR$Dates %in% as.Date(D3),]
rownames(SP_FF_TR)<- format( SP_FF_TR$Dates, format="%Y-%m")
SP_FF_TR<- data.frame(SP_FF_TR)
SP3<- SP_FF_TR[,2]
S3<- data.frame(SP3)
rownames(S3) <- format( SP_FF_TR$Dates, format="%Y-%m")
 
S_a<- data.frame(merge(S1, S2, by="row.names"))

#S_a<- cbind(S2, S1[2:nrow(S1),])
S3$Row.names<- rownames(S3)
SP<-  data.frame(merge(S_a, S3, by="Row.names"))
rownames(SP)<-SP$Row.names
SP$Row.names<- NULL
S3$Row.names<- NULL
SP<- SP[c(2,3,1)]

colnames(SP)<- colnames(Re_SP_Green_mv)

###for list later:

colnames(S1)<- ("S.P.Green.Bond.Index")
colnames(S2)<- ("S.P.Global.1200.Carbon.Efficient.Index.TR")
colnames(S3)<- ("S.P.Global.1200.Fossil.Fuel.Free.Index.TR")



S1_tr<- data.frame()

S2_tr<- data.frame()

S3_tr<- data.frame()


for (i in 1:nrow(S1)){
    for (j in 1:ncol(S1))
S1_tr[i-1,j]<- (((S1[i,j]-S1[(i-1),j])/S1[(i-1),j]))
}

rownames(S1_tr)<- rownames(S1) [2:length(rownames(S1))]

for (i in 1:nrow(S2)){
    for (j in 1:ncol(S2))
S2_tr[i-1,j]<- (((S2[i,j]-S2[(i-1),j])/S2[(i-1),j]))
}
rownames(S2_tr)<- rownames(S2) [2:length(rownames(S2))]


for (i in 1:nrow(S3)){
    for (j in 1:ncol(S3))
S3_tr[i-1,j]<- (((S3[i,j]-S3[(i-1),j])/S3[(i-1),j]))
}
rownames(S3_tr)<- rownames(S3) [2:length(rownames(S3))]



SP_tr<- data.frame()

for (i in 1:nrow(SP)){
    for (j in 1:ncol(SP))
SP_tr[i-1,j]<- (((SP[i,j]-SP[(i-1),j])/SP[(i-1),j]))
}

colnames(SP_tr)<- colnames(SP)
rownames(SP_tr)<- rownames(SP[-1,])


###----------------------------
###----getting shortenned names 
###----------------------------


R_names<- list()
Data_D<- list()
N<- ncol(market_value_DS_GRN)
for (i in 1:N){

R_names=  (paste(sapply(strsplit(as.character(colnames(market_value_DS_GRN)[i]),"\\."), `[`, 1:3), collapse= " "))

Data_D[[i]]<- R_names
All_dat<- do.call(rbind,Data_D)
}
colnames(market_value_DS_GRN)<- NULL
colnames(market_value_DS_GRN)<- All_dat

R_names2<- list()
Data_D2<- list()
N2<- ncol(New_Re_DS_GRN)
for (i in 1:N2){

R_names2=  (paste(sapply(strsplit(as.character(colnames(New_Re_DS_GRN)[i]),"\\."), `[`, 1:3), collapse= " "))

Data_D2[[i]]<- R_names2
All_dat2<- do.call(rbind,Data_D2)
}
colnames(New_Re_DS_GRN)<- NULL
colnames(New_Re_DS_GRN)<- All_dat2


R_names3<- list()
Data_D3<- list()
N3<- ncol(SP_tr)
for (i in 1:N3){

R_names3<-  (paste(sapply(strsplit(as.character(colnames(SP_tr)[i]),"\\."), `[`, 1:3), collapse= " "))

Data_D3[[i]]<- R_names3
All_dat3<- do.call(rbind,Data_D3)
}
colnames(SP_tr)<- NULL
colnames(SP_tr)<- All_dat3






mydocA<- addTitle( mydocA, value=paste("Selected Green Data to Use" ), level = 1 ) 
mydocA<- addParagraph(mydocA, value= "Not all the green data used is complete, many inlcude NA values. Two approaches are taken, firstly, using each index's complete value (excluding all NANS) for calculations of Standard deviations and means, and second, using the minimum available complete section of green indices for calculation of covariances, which require vectors of equal lengths.
The first few columns of each dataset are shown here as an example. For the S&P data, no NANS exist, and density plots are drawn for the dataset.", stylename = "DocDefaults")
mydocA<- addFlexTable(  mydocA,
              (FlexTable( head(New_Re_DS_GRN), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))



###----Getting GREEN Density Plots

New_Re_DS_GRN<- data.frame(New_Re_DS_GRN)
mtlong <- reshape2::melt(New_Re_DS_GRN)

P_Green_Density<- ggplot(mtlong, aes(value)) + facet_wrap(~variable, scales = 'free_x') +
  geom_density()

New_Re_Green_Complete<- New_Re_DS_GRN[complete.cases(New_Re_DS_GRN), ]

market_value_Green_Complete<- New_Re_DS_GRN[complete.cases(New_Re_DS_GRN), ]

mydocA<- addTitle( mydocA, value=paste("Green Data Density Plots" ), level = 1 ) 
mydocA<- addPlot( mydocA , fun=print, x=P_Green_Density)  
mydocA<- addTitle( mydocA, value=paste("Green Data, Complete Dataset" ), level = 1 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( head(New_Re_Green_Complete), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


###----Getting S&P Density Plots

SP_tr<- data.frame(SP_tr)
mtlong <- reshape2::melt(SP_tr)

P_SP_Density<- ggplot(mtlong, aes(value)) + facet_wrap(~variable, scales = 'free_x') +
  geom_density()

mydocA<- addTitle( mydocA, value=paste("S&P Green Density Plots" ), level = 1 ) 
mydocA<- addPlot( mydocA , fun=print, x=P_Green_Density)  
mydocA<- addTitle( mydocA, value=paste("S&P Green Data, Complete Dataset" ), level = 1 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( head(SP_tr), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))






###------------------------------------------------------------------
###------------------------------------------------------------------
###----ALL STAT WORK FOR GREEN AND CONV EXCLUDING SHEET 3 (S&P)
###------------------------------------------------------------------
###------------------------------------------------------------------


Green_ER<- colMeans(New_Re_Green_Complete)
Green_ALL_ER<- colMeans(New_Re_DS_GRN, na.rm = TRUE)
Conv_ER<- colMeans(New_Re)
SP_ER<-colMeans(SP_tr)

Cov_Conv<- cov(New_Re)
Cor_Conv<- cor(New_Re)

Cov_SP<- cov(SP_tr)
Cor_SP<- cor(SP_tr)

Cov_GR<- cov(New_Re_Green_Complete)
rownames(Cov_GR)<- All_dat2
colnames(Cov_GR)<- All_dat2

Cor_GR<- cor(New_Re_Green_Complete)
rownames(Cor_GR)<- All_dat2
colnames(Cor_GR)<- All_dat2

mydocA<- addTitle( mydocA, value=paste("Covariance, Correlations and Expected Returns" ), level = 1 ) 

mydocA<- addTitle( mydocA, value=paste("Expected Returns of Conventional data" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(Conv_ER,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


mydocA<- addTitle( mydocA, value=paste("Expected Returns of Completed Green data" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(Green_ER,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


mydocA<- addTitle( mydocA, value=paste("Expected Returns of All Green data" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(Green_ALL_ER,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))



mydocA<- addTitle( mydocA, value=paste("Expected Returns of All S&P Data" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(SP_ER,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))





mydocA<- addTitle( mydocA, value=paste("Green Covariance" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cov_GR,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

mydocA<- addTitle( mydocA, value=paste("Green Corelation" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cor_GR,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


mydocA<- addTitle( mydocA, value=paste("Conventional Covariance" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cov_Conv,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

mydocA<- addTitle( mydocA, value=paste("Conventional Corelation" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cor_Conv,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


mydocA<- addTitle( mydocA, value=paste("S&P Covariance" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(cov(SP_tr),4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

mydocA<- addTitle( mydocA, value=paste("S&P Corelation" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(cor(SP_tr),4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))




##-------PRINCIPAL COMPONENT ANALYSIS
fit_C <- princomp(Cor_Conv, cor=TRUE)
summary(fit_C) # print variance accounted for 
loadings(fit_C) # pc loadings 
p1_Conv<- plot(fit_C,type="lines") # scree plot 
mydocA<- addTitle( mydocA, value=paste("Principal Component Analysis"), level = 1 ) 
#mydocA<- addTitle( mydocA, value=paste("Conventional PCA, Scree Plot" ), level = 2 ) 
#mydocA<- addPlot( mydocA , fun=print, x=plot(fit_C,type="lines"))  

fit_C$scores # the principal components
p2_Conv<- biplot(fit_C)
#mydocA<- addTitle( mydocA, value=paste("Conventional PCA, Biplot" ), level = 2 ) 
#mydocA<- addPlot( mydocA , fun=print, x=biplot(fit_C))  


fit_G <- princomp(Cor_GR, cor=TRUE)
summary(fit_G) # print variance accounted for 
loadings(fit_G) # pc loadings 
plot(fit_G,type="lines") # scree plot 
#mydocA<- addTitle( mydocA, value=paste("Green PCA, Scree Plot" ), level = 2 ) 
#mydocA<- addPlot( mydocA , fun=print, x=plot(fit_G,type="lines"))  

fit_G$scores # the principal components
biplot(fit_G)
#mydocA<- addTitle( mydocA, value=paste("Green PCA, Biplot" ), level = 2 ) 
#mydocA<- addPlot( mydocA , fun=print, x=biplot(fit_G))  



#cbind.fill(New_Re, New_Re_Green_Complete)
#head( New_Re_Green_Complete)

p333.pryr %<a-% { plot(New_Re)}
p444.pryr %<a-% {plot(New_Re_Green_Complete)}
p555.pryr %<a-% {plot(SP_tr)}

mydocA<- addTitle( mydocA, value=paste("Conventional, Green and S&P Indices illustrated corrleations" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=function() p333.pryr) 
mydocA<- addPlot( mydocA , fun=function() p444.pryr) 
mydocA<- addPlot( mydocA , fun=function() p555.pryr) 





Conv_pca <- prcomp(New_Re , scale = TRUE)
GR_pca <- prcomp(New_Re_Green_Complete , scale = TRUE)
SP_pca <- prcomp(SP_tr , scale = TRUE)

T1<- (summary(Conv_pca))
mydocA<- addTitle( mydocA, value=paste("Conventional PCA, Summary" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(T1$importance,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))


T2<- (summary(GR_pca))

mydocA<- addTitle( mydocA, value=paste("Green PCA, Summary" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(T2$importance,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))



T3<- (summary(SP_pca))

mydocA<- addTitle( mydocA, value=paste("S&P PCA, Summary" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(T3$importance,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))



p3b.pryr %<a-% { biplot(Conv_pca, scale.=0)}
#mydocA<- addTitle( mydocA, value=paste("Conventional Biplot" ), level = 2 ) 
#mydocA<- addPlot( mydocA , fun=print, x=biplot(Conv_pca, scale.=0))  

p4b.pryr %<a-% {biplot(GR_pca, scale.=0)}
#mydocA<- addTitle( mydocA, value=paste("Green Biplot" ), level = 2 ) }
#mydocA<- addPlot( mydocA , fun=print, x=biplot(GR_pca, scale.=0))  

p5b.pryr %<a-% { biplot(SP_pca, scale.=0)}
#writeDoc(mydocA, file = 'Testing.docx')
#browseURL("Testing.docx")



mydocA<- addTitle( mydocA, value=paste("PCA Analysis: Outlying/ Main Affecting Date Identification" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=function() p3b.pryr) 
mydocA<- addPlot( mydocA , fun=function() p4b.pryr) 
mydocA<- addPlot( mydocA , fun=function() p5b.pryr) 



###-----------------------------------------------------------
###-------Using binding function for here and later use:
###-----------------------------------------------------------
#install.packages("rje")
#library(rje)



#R_c<-  colnames(New_Re)

#New_Re_DS_GRN<- New_Re_DS_GRN[,-(ncol(New_Re_DS_GRN))]
#SP_tr<- SP_tr

#R_G<-  colnames(New_Re_DS_GRN)
#R_SP<- colnames(SP_tr)


#All_n<- c(R_c,R_G,R_SP)

#Ccols<- list()

#for (i in 2:length(All_n)){
#cols <- combn( (All_n), i)
#Ccols[[i]]<- cols
#}



#GG1<- rbind(as.matrix(colnames(New_Re_DS_GRN)),as.matrix(colnames(New_Re)),as.matrix(colnames(SP_tr)))
#colnames(SP_tr)
#colnames(New_Re)



#GG<- colnames(New_Re)
#Var<- list()
#for (i in 1:ncol(New_Re)){
#Var[i]<- paste0(GG[i])
#K<- data.frame( New_Re[,i] )

#DD<- as.Date(rownames(New_Re))
#DD_C<- format( DD, "%Y-%m")

#rownames(K)<- DD_C
#colnames(K)<- GG[i]
#assign(Var[[i]], K)

#}



#GG<- colnames(New_Re_DS_GRN)
#Var_G<- list()
#for (i in 1:ncol(New_Re_DS_GRN)){
#Var_G[i]<- paste0(GG[i])
#K<- data.frame( New_Re_DS_GRN[,i] )

#DD<- as.Date(rownames(New_Re_DS_GRN))
#DD_G<- format( DD, format="%Y-%m")

#rownames(K)<- DD_G
#colnames(K)<- GG[i]
#assign(Var_G[[i]], K)

#}

#GG<- colnames(SP_tr)
#Var_SP<- list()
#for (i in 1:ncol(SP_tr)){
#Var_SP[i]<- paste0(GG[i])
#K<- data.frame( SP_tr[,i] )
#DD<- as.Date(rownames(SP_tr))
#DD_SP<- format( DD, format="%Y-%m")

#rownames(K)<- DD_SP
#colnames(K)<- GG[i]
#assign(Var_SP[[i]], K)

#}

##powerSet(GG, rev = FALSE)###-----WORKS, BUT TOO BIG

#do.call()

#cbind(t, z[match(rownames(t), rownames(z),rownames(g))])


#New__Comp<- Bind_Down(New_Re_Green_Complete, New_Re)

DD1<- (rownames(SP_tr))
#DD1<- format( DD, format="%Y-%m")
rownames(SP_tr)<- DD1


DD2<- as.Date(rownames(New_Re_Green_Complete))
DD22<- format( DD2, "%Y-%m")
rownames(New_Re_Green_Complete)<- DD22


DD3<- as.Date(rownames(New_Re))
DD13<- format( DD3, format="%Y-%m")
rownames(New_Re)<- DD13
New_Re$Date<- NULL
New_Re_Green_Complete$Date<- NULL
SP_tr$Date<- NULL


Alldat<- list(New_Re,New_Re_Green_Complete,SP_tr)

New__Comp<- data.frame()

New__Comp<- transform(Reduce(merge, lapply(Alldat, function(x) data.frame(x, rn = row.names(x)))), row.names=rn, rn=NULL)


Cov_ALL<- cov(New__Comp)
Cor_ALL<- cor(New__Comp)
all.pca<- prcomp(New__Comp , scale = TRUE)

ALL_pca <- summary(prcomp(New__Comp , scale = TRUE))

mydocA<- addTitle( mydocA, value=paste("Binding of Complete Green and Conventional Data" ), level = 2 ) 
mydocA<- addParagraph(mydocA, value= "Following the explanation of complete green data, in order to bind the two datasets (complete green and conventional) the corresponsing
  time frame between the two must be defined. The dates of the two data sets are compared, and rows with dates with the same Years and Month are selected, insuring that the 
data is monthly even if the exact day of the month does not correspond. Later to compare each green index to all the conventional ones, the same operation if performed, 
without the need to only include the Complete green dataset, the comparison of dates will automatically create the range of conventional data that corresponds to
the available time range of the green index. The Covariance is shown bellow. ", stylename = "DocDefaults")
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cov_ALL,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

mydocA<- addTitle( mydocA, value=paste("All Data PCA, Summary" ), level = 2 ) 
mydocA<- addFlexTable(  mydocA,
              (FlexTable( data.frame(round(ALL_pca$importance,4)), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))
###------------------------------------------------------------------------------------------------------------------------------

##---------using Decathlon example:

#decathlon2.active<- DF[1:(nrow(DF)-0.2*(nrow(DF))), 4:6]
res.pca <- Conv_pca
resG.pca<- GR_pca
names(res.pca)
head(res.pca$sdev)
head(unclass(res.pca$rotation))


# Eigenvalues
eig <- (res.pca$sdev)^2
# Variances in percentage
variance <- eig*100/sum(eig)
# Cumulative variances
cumvar <- cumsum(variance)
eig.decathlon2.active <- data.frame(eig = eig, variance = variance,
                     cumvariance = cumvar)
head(eig.decathlon2.active)

summary(res.pca)


eig.val <- get_eigenvalue(res.pca)
head(eig.val)

v_GR<- barplot(eig.decathlon2.active[, 2], names.arg=1:nrow(eig.decathlon2.active), 
       main = "Variances",
       xlab = "Principal Components",
       ylab = "Percentage of variances",
       col ="steelblue")
# Add connected line segments to the plot
lines(x = 1:nrow(eig.decathlon2.active), 
      eig.decathlon2.active[, 2], 
      type="b", pch=19, col = "red")


fv_scr_Conv<- fviz_screeplot(res.pca, ncp=10)

mydocA<- addTitle( mydocA, value=paste("Conventional PCA, Scree Plot" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=fv_scr_Conv) 

fv_scr_Gr<- fviz_screeplot(GR_pca, ncp=10)
mydocA<- addTitle( mydocA, value=paste("Green PCA, Scree Plot" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=fv_scr_Gr) 

fv_scr_ALL<- fviz_screeplot(all.pca, ncp=10)
mydocA<- addTitle( mydocA, value=paste("ALL Data PCA, Scree Plot" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=fv_scr_ALL) 

fviz_screeplot(res.pca, ncp=10, choice="eigenvalue")

var_conv <- get_pca_var(res.pca)
var_Gr<- get_pca_var(GR_pca)

Contrb_Gr<- var_Gr$contrib
Contrb_Conv<- var_conv$contrib
cor_Gr<- var_Gr$cor
cor_Conv<- var_conv$cor

coord_Gr<- var_Gr$coord
coord_Conv<- var_conv$coord

Cos2_Gr<- var_Gr$Cos2
Cos2_Conv<- var_conv$Cos2


# Helper function : 
# Correlation between variables and principal components
var_cor_func <- function(var.loadings, comp.sdev){
  var.loadings*comp.sdev
  }
# Variable correlation/coordinates
loadings <- res.pca$rotation
sdev <- res.pca$sdev
var.coord <- var.cor <- t(apply(loadings, 1, var_cor_func, sdev))
head(var.coord)

# Plot the correlation circle
a <- seq(0, 2*pi, length = 100)
plot( cos(a), sin(a), type = 'l', col="gray",
      xlab = "PC1",  ylab = "PC2")
abline(h = 0, v = 0, lty = 2)
# Add active variables
arrows(0, 0, var.coord[, 1], var.coord[, 2], 
      length = 0.1, angle = 15, code = 2)
# Add labels
text(var.coord, labels=rownames(var.coord), cex = 1, adj=1)
fviz_pca_var(res.pca)



pca_conv<- fviz_pca_var(res.pca, col.var="contrib")+
scale_color_gradient2(low="blue",  mid="yellow", 
      high="red", midpoint=55) + theme_minimal()
mydocA<- addTitle( mydocA, value=paste("Conventional PCA, Biplot" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=pca_conv) 


pca_Gr<- fviz_pca_var(resG.pca, col.var="contrib") +
scale_color_gradient2(low="blue",  mid="yellow", 
      high="red", midpoint=55) + theme_minimal()
mydocA<- addTitle( mydocA, value=paste("Green PCA, Biplot" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=pca_Gr) 



pca_SP<- fviz_pca_var(SP_pca, col.var="contrib") +
scale_color_gradient2(low="blue",  mid="yellow", 
      high="red", midpoint=55) + theme_minimal()
mydocA<- addTitle( mydocA, value=paste("S&P PCA, Biplot" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=pca_SP) 






pca_ALL<- fviz_pca_var(all.pca, col.var="contrib") +
scale_color_gradient2(low="blue",  mid="yellow", 
      high="red", midpoint=55) + theme_minimal()
mydocA<- addTitle( mydocA, value=paste("All PCA, Biplot" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=pca_ALL) 

###---------------ALL DATES PCA


mydocA<- addTitle( mydocA, value=paste("Timeseries Analysis of Indices" ), level = 2 ) 
mydocA<- addParagraph(mydocA, value= " Having completed the PCA of the Indices, it would be interesting to see how the addition of green indices
to a conventional dataframe alters the effects of variations through time. Although the timespans will differ due to different available data ranges, it may be 
possible that inclusion of indices minimize the weight of events significantly altering the trends of the conventional data, and vice versa, changing the time dependency",
 stylename = "DocDefaults")





ind.coord <- all.pca$x
head(ind.coord)

center <- all.pca$center
scale<- all.pca$scale
getdistance <- function(ind_row, center, scale){
  return(sum(((ind_row-center)/scale)^2))
  }
#d2 <- apply(decathlon2.active,1,getdistance, center, scale)
# Compute the cos2
#cos2 <- function(ind.coord, d2){return(ind.coord^2/d2)}
#ind.cos2 <- apply(ind.coord, 2, cos2, d2)
#head(ind.cos2)



# Contributions of individuals
contrib <- function(ind.coord, comp.sdev, n.ind){
  100*(1/n.ind)*ind.coord^2/comp.sdev^2
}
ind.contrib <- t(apply(ind.coord,1, contrib, 
                       all.pca$sdev, nrow(ind.coord)))
head(ind.contrib[, 1:3])



p3.pryr %<a-% {plot(ind.coord[,1], ind.coord[,2], pch = 19,  
     xlab="PC1 - 41.2%",ylab="PC2 - 18.4%")
abline(h=0, v=0, lty = 2)
text(ind.coord[,1], ind.coord[,2], labels=rownames(ind.coord),
        cex=0.7, pos = 3)}


mydocA<- addTitle( mydocA, value=paste("All binded Data(Green and Conventional): Date Contribution" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=function() p3.pryr) 


###---------------CONV DATES PCA


ind.coord <- res.pca$x
head(ind.coord)

center <- res.pca$center
scale<- res.pca$scale
getdistance <- function(ind_row, center, scale){
  return(sum(((ind_row-center)/scale)^2))
  }
#d2 <- apply(decathlon2.active,1,getdistance, center, scale)
# Compute the cos2
#cos2 <- function(ind.coord, d2){return(ind.coord^2/d2)}
#ind.cos2 <- apply(ind.coord, 2, cos2, d2)
#head(ind.cos2)



# Contributions of individuals
contrib <- function(ind.coord, comp.sdev, n.ind){
  100*(1/n.ind)*ind.coord^2/comp.sdev^2
}
ind.contrib <- t(apply(ind.coord,1, contrib, 
                       res.pca$sdev, nrow(ind.coord)))
head(ind.contrib[, 1:3])




p1.pryr %<a-% { plot(ind.coord[,1], ind.coord[,2], pch = 19,  
     xlab="PC1 - 41.2%",ylab="PC2 - 18.4%")
abline(h=0, v=0, lty = 2)
text(ind.coord[,1], ind.coord[,2], labels=rownames(ind.coord),
        cex=0.7, pos = 3)
}

mydocA<- addTitle( mydocA, value=paste("Conventional Data: Date Contribution" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=function() p1.pryr) 

###---------------Green DATES PCA

ind.coord <- resG.pca$x
head(ind.coord)

center <- resG.pca$center
scale<- resG.pca$scale
getdistance <- function(ind_row, center, scale){
  return(sum(((ind_row-center)/scale)^2))
  }
#d2 <- apply(decathlon2.active,1,getdistance, center, scale)
# Compute the cos2
#cos2 <- function(ind.coord, d2){return(ind.coord^2/d2)}
#ind.cos2 <- apply(ind.coord, 2, cos2, d2)
#head(ind.cos2)



# Contributions of individuals
contrib <- function(ind.coord, comp.sdev, n.ind){
  100*(1/n.ind)*ind.coord^2/comp.sdev^2
}
ind.contrib <- t(apply(ind.coord,1, contrib, 
                       resG.pca$sdev, nrow(ind.coord)))
head(ind.contrib[, 1:3])


p2.pryr %<a-% {
plot(ind.coord[,1], ind.coord[,2], pch = 19,  
     xlab="PC1 - 41.2%",ylab="PC2 - 18.4%")
abline(h=0, v=0, lty = 2)
text(ind.coord[,1], ind.coord[,2], labels=rownames(ind.coord),
        cex=0.7, pos = 3)
}
mydocA<- addTitle( mydocA, value=paste("Green Data: Date Contribution" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=function() p2.pryr) 


##---------correcting for skewness etc:
require(caret)
trans = preProcess(New_Re[,1:ncol(New_Re)], 
                   method=c("BoxCox", "center", 
                            "scale", "pca"))

PC = predict(trans, New_Re)
model <- train(New_Re[,1:ncol(New_Re)], method='lda', preProcess='pca')
trans$rotation
biplot(x=x1, y=PC, scale.=0)
###----------------------------------------------------------------------------------------------------------------------------
###--------------------------Normalizing and attempting to add to word, FAILED, SAVED TO PDF-----------------------------------
###----------------------------------------------------------------------------------------------------------------------------


colnames(New_Re)
set.seed(1)
#predictors = data.frame(New_Re[,1:11])
New_Re$Date<- (rownames(New_Re))

plot_list = list()
#mydoc2 = docx()
mydocA<- addTitle( mydocA, value=paste("Correcting for Skewness via Box Cox Power Function" ), level = 1 ) 


for (i in 1:(length(colnames(New_Re))-1)){

predictors= data.frame(x1 = New_Re$Date, 
                        x2 = New_Re[colnames(New_Re)[i]])
colnames(predictors)<- c("x1", "x2")
p1<- ggplot(predictors, aes(x = x1, y = x2)) + geom_point()

temp <- melt(predictors, measured = c("x1", "x2"))
p2<- ggplot(temp) + geom_histogram(aes(x=value)) + 
  facet_grid(. ~ variable, scales = "free_x")

grid.arrange(p1, p2)
trans <- preProcess(predictors, c("BoxCox", "center", "scale"))
predictors_trans <- data.frame(trans = predict(trans, predictors))

p3<- ggplot(predictors_trans) + geom_point(aes(x = trans.x1, y = trans.x2))
temp <- melt(predictors_trans, measured = c("trans.x1", "trans.x2"))
p4<- ggplot(temp) + geom_histogram(aes(x=value), data = temp) + 
  facet_grid(. ~ variable, scales = "free_x")
grid.arrange(p3, p4)
#title(cat("Normalization of Index", colnames(New_Re)[i]))

#pdf("filename.pdf", width = 8, height = 12) 
plot_list[[i]] =  (grid.arrange(p1, p2, p3, p4))

p4.pryr %<a-% {(grid.arrange(p1, p2, p3, p4))}
g1<- do.call("grid.arrange", plot_list[[i]]) 
#ggsave("sgcirNIR.jpg")

mydocA<- addTitle( mydocA, value=paste("Correcting for Skewness via Box Cox Power Function", colnames(New_Re)[i] ), level = 2 ) 
mydocA<- addPlot( mydocA , fun = function() p4.pryr)#, 
 #vector.graphic = TRUE, par.properties = parCenter(), width = 6, heigth = 7 )


     }


#writeDoc(mydocA, file = 'testa.docx')
#browseURL("testa.docx")


pdf("plots1234.pdf", onefile = TRUE)
for (i in 1:length(plot_list)){
#:length(colnames(New_Re))-1)
  do.call("grid.arrange", plot_list[[i]])  

}
dev.off()

g2<- grid.draw(g1)

#mydoc = docx()

#base_legend = "My first plot"

#for( index in 1:3 ){
  #mylegend = pot(base_legend, textBoldItalic() )

  #if( index > 1 ) mylegend = paste0(base_legend, " (cont'd)" )
  #else mylegend = base_legend

  #mydoc = addPlot( doc = mydoc, fun = print, x = grid.arrange(plot_list[[index]])  , 
    #vector.graphic = TRUE, par.properties = parCenter(), width = 6, heigth = 7 )

 # mydoc = addParagraph( mydoc, value = mylegend, stylename = "rPlotLegend")
#}
#writeDoc( mydoc, "why2.docx")
#browseURL( "why2.docx" )
##---------------------------------------------------------

#g <- ggbiplot(DF.pca, obs.scale = 1, var.scale = 1, 
 #             groups = DF$Asset, ellipse = TRUE, 
  #            circle = TRUE)


g <- ggbiplot(all.pca, obs.scale = 1, var.scale = 1, 
              groups = NULL, ellipse = TRUE, 
              circle = TRUE)
g <- g + scale_color_discrete(name = '')
g <- g + theme(legend.direction = 'horizontal', 
               legend.position = 'top')

g<- ggbiplot(Conv_pca, choices = 1:2, scale = 1, pc.biplot = TRUE, obs.scale = 1 - scale, var.scale = scale, groups = NULL, ellipse = TRUE, ellipse.prob = 0.68, labels =FALSE, labels.size = 3, alpha = 1, var.axes = TRUE, circle  = TRUE, circle.prob = 0.69, varname.size = 3, varname.adjust = 1.5, varname.abbrev = FALSE)

print(g)

###------------------------------------------------
##----------Plotting all data----------------------
###------------------------------------------------

mtlong <- reshape2::melt(New_Re_Green_Complete)

ggplot(mtlong, aes(value)) + facet_wrap(~variable, scales = 'free_x') +
  geom_density()

df <- melt(New_Re ,  id.vars = 'Date', variable.name = 'series')
all_Cov1<- ggplot(df, aes(Date,value, group = 1)) + geom_line(aes(colour = series))

mydocA<- addTitle( mydocA, value=paste("Total Returns" ), level = 1 ) 

mydocA<- addTitle( mydocA, value=paste("Total Conventional Returns" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=all_Cov1)  
all_Cov2<- ggplot(df, aes(Date,value, group = 1)) + geom_line() + facet_grid(series ~ .)
mydocA<- addPlot( mydocA , fun=print, x=all_Cov2)  

New_Re_Green_Complete$Date<- rownames(New_Re_Green_Complete)
df <- melt(New_Re_Green_Complete ,  id.vars = 'Date', variable.name = 'series')
all_Green1<- ggplot(df, aes(Date,value, group = series)) + geom_line(aes(colour = series))
mydocA<- addTitle( mydocA, value=paste("Total Green Returns" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=all_Green1)  

all_Green2<- ggplot(df, aes(Date,value, group = series)) + geom_line() + facet_grid(series ~ .)
mydocA<- addPlot( mydocA , fun=print, x=all_Green2)  


SP_tr$Date<- rownames(SP_tr)
df <- melt(SP_tr ,  id.vars = 'Date', variable.name = 'series')
all_SP_tr<- ggplot(df, aes(Date,value, group = series)) + geom_line(aes(colour = series))
mydocA<- addTitle( mydocA, value=paste("Total S&P Returns" ), level = 2 ) 
mydocA<- addPlot( mydocA , fun=print, x=all_SP_tr)  

all_SP_tr2<- ggplot(df, aes(Date,value, group = series)) + geom_line() + facet_grid(series ~ .)
mydocA<- addPlot( mydocA , fun=print, x=all_SP_tr2)  




####-----------------------------------------------------------------------------------------------------------------------------------------
####--------------------Comparison of Green and conventional, creating matching numbers based on year and month,02-10-2017-------------------
####-----------------------------------------------------------------------------------------------------------------------------------------


FTS4G<- New_Re_DS_GRN[3]
#X<- FTS4G
#Y<- New_Re

#New_Re_Green_Complete_Y<-  (year(rownames(X)))
#New_Re_Green_Complete_M<- month(rownames(X))

#New_Re_Green_Complete_dates<- data.frame(cbind(New_Re_Green_Complete_M, New_Re_Green_Complete_Y))
#colnames(New_Re_Green_Complete_dates)<- c("M" , "Y")

#New_Re_Y<- (year(rownames(Y)))
#New_Re_M<- month(rownames(Y))

#New_Re_dates<- data.frame(cbind(New_Re_M, New_Re_Y))
#colnames(New_Re_dates)<- c("M" , "Y")
#New_Re_CMN_D<- inner_join(New_Re_dates, New_Re_Green_Complete_dates)

#if (length(New_Re_CMN_D)!=length(New_Re_dates)){
#cat("The Green and Conventional Matrixes were not the same size, Conv was ",(length(New_Re_CMN_D)-length(New_Re_dates)), "more than green, so matched dates extracted")
#}


#Y$Date<- rownames(Y)
#Comp_Y<- data.frame(matrix(, nrow=nrow(New_Re_CMN_D), ncol= ncol(Y)))
#Comp_X<- data.frame(matrix(, nrow=nrow(New_Re_CMN_D), ncol= ncol(X)))

#for (i in 1:nrow(New_Re_CMN_D)){
#Comp_Y[i,]<- subset(Y, ( (month(rownames(Y)))==New_Re_CMN_D[i,1] & year(rownames(Y))==New_Re_CMN_D[i,2]))
#}

#for (i in 1:nrow(New_Re_CMN_D)){
#Comp_X[i,]<- subset(X, ( (month(rownames(X)))==New_Re_CMN_D[i,1] & year(rownames(X))==New_Re_CMN_D[i,2]))
#}

#rownames(Comp_Y)<- Comp_Y[, ncol( Comp_Y)]
#colnames(Comp_Y)<- colnames(Y)
#Comp_Y["Date"]<- NULL

#rownames(Comp_X)<- Comp_X[, ncol( Comp_X)]
#colnames(Comp_X)<- colnames(X)
#Comp_X["Date"]<- NULL


#FTS4G<- Comp_X
#New_Re<- Comp_Y

if(nrow(FTS4G)!=nrow(New_Re)){
cat("Nope, The Green and Conventional Matrixes are not matched correctly, Conv has ",(nrow(FTS4G)-nrow(New_Re)), "more than green, fix it")
}###-------!!!!!!!!

###-----------------------RUN TESTS

PP.test(New_Re[,1])
kpss.test(New_Re[,1])
adf.test(New_Re[,1])


#mydoc <- docx( ) #%>% 

for (i in 1:ncol(New__Comp)) {

Tab1<- (PP.test(New__Comp[,i]))
Tab2<- kpss.test(New__Comp[,i])
Tab3<- adf.test(New__Comp[,i])

Tab_all <- capture.output(print(Tab1), print(Tab2), print(Tab3))
##Tab4<- rbind(Tab1, Tab2, Tab3)

addTitle( mydocA, value=paste("Test Results for", colnames(New__Comp)[i] ), level = 1 )%>%  
addParagraph( value=Tab_all, stylename = "DocDefaults" )# %>%

#addFlexTable(mydoc,  Tab1 %>%
                #  FlexTable( header.cell.props = cellProperties( background.color =  "#003366" ),
                            # header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                            # add.rownames = TRUE ) %>%
                 # setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ) 
}
 
#writeDoc(mydocA, file = '08-10.docx')
# open the Word document
#browseURL("08-10.docx")


###---bind green and conv together for simon------
mydocA<- addTitle( mydocA, value=paste("Binding Green Indices to Conventional for Comparison" ), level = 1 ) 
mydocA<- addParagraph(mydocA, 
         value= "To help determine which indices should be added to which conventional portfolios for the Black Litterman Analysis, each green index
is added to the risky asset portfolio, and the overall covariances are compared. The difference between these covariances and the previous All Data 
covariance lies in that for each index, the conventional range is set to the range of dates available for the individual green index being added,
as opposed to the length of the complete green indices. One column of Risky assets is also added to the indices, the value of which is the sum of
the conventional asset returns at any date, the same rule is applied to its market value. To accuratley measure the covariance
throughout the timeseries, the covariance is measured through rolling windows of length time series divided by 20. The windows of covariance roll over
the data to insure connectivity and avoid misrepresentation of jumps associated with window transaction with that of covariance volitlity. 
The same applies to standard deviation", 
         stylename = "DocDefaults")
New_Re<- New_Re[,1:(ncol(New_Re)-1)]
New_Re$Risky_Asset<- rowSums(New_Re)
#New_Re$Date<- as.Date(rownames(New_Re))

#New_Re_Green_Complete$Date<- as.Date(rownames(New_Re_Green_Complete))
#Re_dat$Date<- as.Date(rownames(Re_dat))

merge(FTS4G, New_Re,by=0)###--all data


DD<- as.Date(rownames(FTS4G))
DD1<- format( DD, format="%Y-%m")
rownames(FTS4G)<- DD1

Kb1<- list(New_Re, FTS4G)

RA_FTS4G<- transform(Reduce(merge, lapply(Kb1, function(x) data.frame(x, rn = row.names(x)))), row.names=rn, rn=NULL)

width<- floor(nrow(New_Re)/20)
#width<- 2
Cov_roll_New_Re<- roll_cov(as.matrix(New_Re), width, weights = rep(1, width))#, center = TRUE,
Cov.dat_New_Re<- cov(as.matrix(New_Re))

#Cov_roll_SP<- roll_cov(as.matrix(SP_tr), width, weights = rep(1, width))#, center = TRUE,
#Cov.dat_SP<- cov(as.matrix(SP_tr))


Cor_roll_New_Re<- roll_cor(as.matrix(New_Re), width, weights = rep(1, width))# , center = TRUE,
#scale = FALSE, min_obs = width, complete_obs = TRUE,
#na_restore = FALSE, parallel_for = c("rows", "cols"))

Cor_roll_RA_FT<- roll_cor(as.matrix(RA_FTS4G), width, weights = rep(1, width))# , center = TRUE,
Cov_roll_RA_FT<- roll_cov(as.matrix(RA_FTS4G), width, weights = rep(1, width))#, center = TRUE,
Sd_roll_RA_FT<- roll_sd(as.matrix(RA_FTS4G), width, weights = rep(1, width))


Sd_roll_New_Re<- roll_sd(as.matrix(New_Re), width, weights = rep(1, width))
DF_Cor<- data.frame(Cor_roll_RA_FT)



###-------------Get Elements of Cor and Cov Rolled Matrixes (Upper Traingular)

N_m<- dim(Cov_roll_RA_FT)[1]
Windows<- dim(Cov_roll_RA_FT)[3]
rows <- N_m 


x <- rev(abs(sequence(seq.int(rows - 1)) - rows) + 1)
y <- rep.int(seq.int(rows - 1), rev(seq.int(rows - 1)))

idx <- cbind(y, x)

Nms<- vector()

Cov_Dat<- data.frame(matrix(,  nrow= Windows, ncol= nrow(idx)))
colnames(Cov_Dat)<- t(c(apply(format(idx), 1, paste, collapse=",")))

##---remove dates from dat Frames and bind FTSE$GOOD AND RISKY ASSETS:

G_N<- colnames(New_Re_DS_GRN)
New_Re_DS_GRN$Date<- rownames(New_Re_DS_GRN) 



idkk<-data.frame()

for (i in 1:nrow(idx) ){
idkk[i,1]<- colnames(RA_FTS4G)[idx[i,1]]
idkk[i,2]<- colnames(RA_FTS4G)[idx[i,2]]
}

colnames(Cov_Dat)<- t(c(apply(format(idkk), 1, paste, collapse=",")))

for (i in 1:nrow(idx) ){
Cov_Dat[,i]<- Cov_roll_RA_FT[idx[i,1], idx[i,2], ]
}

Cov.dat<- cov(RA_FTS4G)
Cov_Dat<- Cov_Dat[complete.cases(Cov_Dat), ]
Cov_Dat$D<- rownames(Cov_Dat)
df <- melt(Cov_Dat ,  id.vars = 'D', variable.name = 'series')

#P_Cor_Dat<- ggplot(df, aes(D,value, group=series)) +  geom_line(aes(colour = series))


P_Cov_Dat<- ggplot(df, aes(D,value,, group=series)) + geom_line(aes(colour = series))
(aes(colour = series))#+stat_smooth()


####---bind market values:

market_value_DS_GRN<- Re_DS_Green2[names(Re_DS_Green2 %>% select(contains("MARKET.VALUE")))]

market_value_DS_GRN<- market_value_DS_GRN[-1,1:2]
market_value$Risky_assets<- rowSums(market_value)

FTS4G_mv<- data.frame(market_value_DS_GRN[,1])
rownames(FTS4G_mv)<- rownames(market_value_DS_GRN)


 duplicated(rownames(FTS4E_mv))

FTS4E_mv<- data.frame(market_value_DS_GRN[,2])
rownames(FTS4E_mv)<- rownames(market_value_DS_GRN)

RA_FTS4G_mv<- cbind(market_value, FTS4G_mv)
RA_FTS4E_mv<- cbind(market_value,FTS4E_mv)


RA_FTS4G_mv<- RA_FTS4G_mv[complete.cases(RA_FTS4G_mv),]
RA_FTS4E_mv<- RA_FTS4E_mv[complete.cases(RA_FTS4E_mv),]

#Green<- cbind(market_value, market_value_DS_GRN[-1,1] )###--all data


###--------------------------------------
##----bind each in loop------------------
###--------------------------------------
Vars<- list()
for (i in 1:(ncol(New_Re_DS_GRN)-1)) {


#FTS4G<- New_Re_DS_GRN[3]

G_S<- data.frame()


DD<- as.Date(rownames(New_Re_DS_GRN))
DD1<- format( DD, format="%Y-%m")
rownames(New_Re_DS_GRN)<- DD1

New_Re_DS_GRN$Date<- DD1

G_S<- data.frame(New_Re_DS_GRN[complete.cases(New_Re_DS_GRN[,i]),i])
New_Re_DS_GRN$Date[complete.cases(New_Re_DS_GRN[,i])]
rownames(G_S)<- New_Re_DS_GRN$Date[complete.cases(New_Re_DS_GRN[,i])]
colnames(G_S)<- G_N[i]
G_Bind1<- list(G_S, New_Re)
G_Bind<- transform(Reduce(merge, lapply(G_Bind1, function(x) data.frame(x, rn = row.names(x)))), row.names=rn, rn=NULL)






assign(paste0("DF_Risky_A_", G_N[i]), data.frame( G_Bind ))
mydocA<- addTitle( mydocA, value=paste0("All Assets and ", G_N[i]), level = 2 ) 
mydocA<- addParagraph(mydocA, value= paste("Common Dates between the Risky assets and " ,G_N[i]), stylename = "DocDefaults")
Tab55<- data.frame(c(rownames(G_Bind)[1],rownames(G_Bind)[nrow(G_Bind)],nrow(G_Bind)))
colnames(Tab55)<- paste("Risky assets and " ,G_N[i])
rownames(Tab55)<- c("Start Date", "End date", "Size")


mydocA<- addFlexTable(  mydocA,
              (FlexTable( Tab55, header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

##mydocA<- addFlexTable(  mydocA,
              ##(FlexTable( stargazer(data.frame(G_Bind)))))



Vars[i]<- paste0("DF_Risky_A_", G_N[i])

mydocA<- addTitle( mydocA, value=paste0("Portfolio of Risky Assets and ", G_N[i]), level = 2 ) 


assign(Vars[[i]], data.frame( G_Bind ))
it<- get(Vars[[i]])

width<- floor(nrow(it)/20)
#width<- 2
it["Date"]<- NULL

Cor_roll_it<- roll_cor(as.matrix(it), width, weights = rep(1, width))
Cov_roll_it<- roll_cov(as.matrix(it), width, weights = rep(1, width))
Sd_roll_it<- roll_sd(as.matrix(it), width, weights = rep(1, width))

Sd_roll_it<- data.frame(Sd_roll_it)

N_m<- dim(Cov_roll_it)[1]
Windows<- dim(Cov_roll_it)[3]
rows <- N_m 


x <- rev(abs(sequence(seq.int(rows - 1)) - rows) + 1)
y <- rep.int(seq.int(rows - 1), rev(seq.int(rows - 1)))

idx <- cbind(y, x)

Nms<- vector()

Cov_Dat<- data.frame(matrix(,  nrow= Windows, ncol= nrow(idx)))
colnames(Cov_Dat)<- t(c(apply(format(idx), 1, paste, collapse=",")))

Cor_Dat<- data.frame(matrix(,  nrow= Windows, ncol= nrow(idx)))
colnames(Cor_Dat)<- t(c(apply(format(idx), 1, paste, collapse=",")))

#G_N<- colnames(New_Re_DS_GRN)
#New_Re_DS_GRN$Date<- rownames(New_Re_DS_GRN) 



idkk<-data.frame()

for (ii in 1:nrow(idx) ){
idkk[ii,1]<- colnames(it)[idx[ii,1]]
idkk[ii,2]<- colnames(it)[idx[ii,2]]
}

colnames(Cov_Dat)<- t(c(apply(format(idkk), 1, paste, collapse=",")))
colnames(Cor_Dat)<- t(c(apply(format(idkk), 1, paste, collapse=",")))


for (iii in 1:nrow(idx) ){
Cov_Dat[,iii]<- Cov_roll_it[idx[iii,1], idx[iii,2], ]
Cor_Dat[,iii]<- Cor_roll_it[idx[iii,1], idx[iii,2], ]
}


###----creating rolling data

Cov_Dat<- Cov_Dat[complete.cases(Cov_Dat), ]
Cov_Dat$D<- rownames(Cov_Dat)


Cor_Dat<- Cor_Dat[complete.cases(Cor_Dat), ]
Cor_Dat$D<- rownames(Cor_Dat)

Sd_roll_it$D <- rownames(Sd_roll_it)
Sd_roll_it<- Sd_roll_it[complete.cases(Sd_roll_it),]# 1:(ncol(Sd_roll_it)-1) ]

df <- melt(Cov_Dat ,  id.vars = 'D', variable.name = 'series')
df1 <- melt(Cor_Dat ,  id.vars = 'D', variable.name = 'series')
df2<- melt(Sd_roll_it,  id.vars = 'D', variable.name = 'series')

##------COV
mydocA<- addTitle( mydocA, value="Manual Covariance", level = 3 ) 
Cov.dat<- cov(it)
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cov.dat,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

P_Cov_Dat<- ggplot(df, aes(D,value, group=series)) + geom_line(aes(colour = series))+ theme(legend.text=element_text(size=7), legend.position="bottom")

(aes(colour = series))
mydocA<- addPlot( mydocA , fun=print, x=P_Cov_Dat)  


##-----COR

mydocA<- addTitle( mydocA, value="Manual Correlation", level = 3 ) 
Cor.dat<- cor(it)
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cor.dat,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))
P_Cor_Dat<- ggplot(df1, aes(D,value, group=series)) + geom_line(aes(colour = series))+ theme(legend.text=element_text(size=7), legend.position="bottom")
(aes(colour = series))
mydocA<- addPlot( mydocA , fun=print, x=P_Cor_Dat)  

#-----STDV
mydocA<- addTitle( mydocA, value="Manual Standard Deviation", level = 3 ) 
stds.dat<- colSds(as.matrix(it))
stds.dat<- data.frame(t(stds.dat))
colnames(stds.dat)<- colnames(it)
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(stds.dat,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

P_stdv_Dat<- ggplot(df2, aes(D,value, group=series)) + geom_line(aes(colour = series))+ theme(legend.text=element_text(size=7), legend.position="bottom")
(aes(colour = series))
mydocA<- addPlot(  mydocA , fun=print, x=P_stdv_Dat)  



}


###--------------------------------------------
###-------------BINDING TO S&P DATA------------
###--------------------------------------------
Vars2<- list()
for (i in 1:(ncol(SP_tr))) {

G_N<- colnames(SP_tr)
#FTS4G<- New_Re_DS_GRN[3]

G_S<- data.frame()

G_S<- data.frame(SP_tr[complete.cases(SP_tr[,i]),i])
SP_tr$Date<- rownames(SP_tr)

rownames(G_S)<- SP_tr$Date[complete.cases(SP_tr[,i])]
colnames(G_S)<- G_N[i]
G_Bind1<- list(G_S, New_Re)
G_Bind<- transform(Reduce(merge, lapply(G_Bind1, function(x) data.frame(x, rn = row.names(x)))), row.names=rn, rn=NULL)


  assign(paste0("DF_Risky_A_", G_N[i]), data.frame( G_Bind ))

Vars2[i]<- paste0("DF_Risky_A_", G_N[i])
mydocA<- addTitle( mydocA, value=paste0("All Assets and ", G_N[i]), level = 2 ) 
mydocA<- addParagraph(mydocA, value= paste("Common Dates between the Risky assets and " ,G_N[i]), stylename = "DocDefaults")
Tab55<- data.frame(c(rownames(G_Bind)[1],rownames(G_Bind)[nrow(G_Bind)],nrow(G_Bind)))
colnames(Tab55)<- paste("Risky assets and " ,G_N[i])
rownames(Tab55)<- c("Start Date", "End date", "Size")

mydocA<- addFlexTable(  mydocA,
              (FlexTable( Tab55, header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

##mydocA<- addFlexTable(  mydocA,
              ##(FlexTable( stargazer(data.frame(G_Bind)))))


assign(Vars2[[i]], data.frame( G_Bind ))
it<- get(Vars2[[i]])
it["Date"]<- NULL
width<- floor(nrow(it)/20)
#width<- 2


Cor_roll_it<- roll_cor(as.matrix(it), width, weights = rep(1, width))
Cov_roll_it<- roll_cov(as.matrix(it), width, weights = rep(1, width))
Sd_roll_it<- roll_sd(as.matrix(it), width, weights = rep(1, width))

Sd_roll_it<- data.frame(Sd_roll_it)

N_m<- dim(Cov_roll_it)[1]
Windows<- dim(Cov_roll_it)[3]
rows <- N_m 


x <- rev(abs(sequence(seq.int(rows - 1)) - rows) + 1)
y <- rep.int(seq.int(rows - 1), rev(seq.int(rows - 1)))

idx <- cbind(y, x)

Nms<- vector()

Cov_Dat<- data.frame(matrix(,  nrow= Windows, ncol= nrow(idx)))
colnames(Cov_Dat)<- t(c(apply(format(idx), 1, paste, collapse=",")))

Cor_Dat<- data.frame(matrix(,  nrow= Windows, ncol= nrow(idx)))
colnames(Cor_Dat)<- t(c(apply(format(idx), 1, paste, collapse=",")))

#G_N<- colnames(New_Re_DS_GRN)
#New_Re_DS_GRN$Date<- rownames(New_Re_DS_GRN) 



idkk<-data.frame()

for (ii in 1:nrow(idx) ){
idkk[ii,1]<- colnames(it)[idx[ii,1]]
idkk[ii,2]<- colnames(it)[idx[ii,2]]
}

colnames(Cov_Dat)<- t(c(apply(format(idkk), 1, paste, collapse=",")))
colnames(Cor_Dat)<- t(c(apply(format(idkk), 1, paste, collapse=",")))


for (iii in 1:nrow(idx) ){
Cov_Dat[,iii]<- Cov_roll_it[idx[iii,1], idx[iii,2], ]
Cor_Dat[,iii]<- Cor_roll_it[idx[iii,1], idx[iii,2], ]
}



###----creating rolling data

Cov_Dat<- Cov_Dat[complete.cases(Cov_Dat), ]
Cov_Dat$D<- rownames(Cov_Dat)


Cor_Dat<- Cor_Dat[complete.cases(Cor_Dat), ]
Cor_Dat$D<- rownames(Cor_Dat)

Sd_roll_it$D <- rownames(Sd_roll_it)
Sd_roll_it<- Sd_roll_it[complete.cases(Sd_roll_it),]# 1:(ncol(Sd_roll_it)-1) ]

df <- melt(Cov_Dat ,  id.vars = 'D', variable.name = 'series')
df1 <- melt(Cor_Dat ,  id.vars = 'D', variable.name = 'series')
df2<- melt(Sd_roll_it,  id.vars = 'D', variable.name = 'series')

##------COV
mydocA<- addTitle( mydocA, value="Manual Covariance", level = 3 ) 
Cov.dat<- cov(it)
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cov.dat,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

P_Cov_Dat<- ggplot(df, aes(D,value, group=series)) + geom_line(aes(colour = series))+ theme(legend.text=element_text(size=7), legend.position="bottom")

(aes(colour = series))
mydocA<- addPlot( mydocA , fun=print, x=P_Cov_Dat)  


##-----COR

mydocA<- addTitle( mydocA, value="Manual Correlation", level = 3 ) 
Cor.dat<- cor(it)
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(Cor.dat,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))
P_Cor_Dat<- ggplot(df1, aes(D,value, group=series)) + geom_line(aes(colour = series))+ theme(legend.text=element_text(size=7), legend.position="bottom")

(aes(colour = series))
mydocA<- addPlot( mydocA , fun=print, x=P_Cor_Dat)  

#-----STDV
mydocA<- addTitle( mydocA, value="Manual Standard Deviation", level = 3 ) 
stds.dat<- colSds(as.matrix(it))
stds.dat<- data.frame(t(stds.dat))
colnames(stds.dat)<- colnames(it)
mydocA<- addFlexTable(  mydocA,
              (FlexTable( round(stds.dat,4), header.cell.props = cellProperties( background.color =  "#003366" ),
                           header.text.props = textProperties( color = "white", font.size = 9, font.weight = "bold" ),
                           body.text.props = textProperties( font.size = 7 ),
                           add.rownames = TRUE ) %>%
                           setZebraStyle( odd = "#DDDDDD", even = "#FFFFFF" ) ))

P_stdv_Dat<- ggplot(df2, aes(D,value, group=series)) + geom_line(aes(colour = series))+ theme(legend.text=element_text(size=7), legend.position="bottom")

(aes(colour = series))
mydocA<- addPlot(  mydocA , fun=print, x=P_stdv_Dat)  




}


writeDoc(mydocA, file = 'k16.docx')
browseURL("k16.docx")

