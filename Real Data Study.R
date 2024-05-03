library(tidyverse)
library(amap)
library(cluster)
library(MASS)
library(EQL)
library(e1071)
library(ggplot2)
library(gogarch)
library(tmvtnorm)
library(expm)
library(matrixStats)
library(matrixNormal)

AKI_diag<-read.csv("../diagnose_AKI_May_iv.csv") #MIMIC-IV AKI Patients Diagnose data
uni_id<-unique(AKI_diag$ICU_ID)
AKI_lab<-read.csv("../lab_AKI_May_iv.csv")  #MIMIC-IV AKI Patients Lab data

endstage_index <- grepl("End stage renal disease", AKI_diag$DIAGNOSE, ignore.case = TRUE)

# drop End stage renal disease
endstage_output <- AKI_diag$ICU_ID[endstage_index ]
drop_endstage_id<-unique(endstage_output)
uni_id_01 <- uni_id[!uni_id %in% drop_endstage_id]
# drop burn
burn_index <- grepl("(?i)\\b(?!heartburn)\\w*burn\\b", AKI_diag$DIAGNOSE, perl = TRUE)
burn_output <- AKI_diag$ICU_ID[burn_index ]
uni_id_02 <-uni_id_01 [!uni_id_01  %in% unique(burn_output)]
# drop renal dialysis
rd_index <- grepl("renal dialysis", AKI_diag$DIAGNOSE, ignore.case = TRUE)
rd_output <- AKI_diag$ICU_ID[rd_index ]
uni_id_03 <-uni_id_02[!uni_id_02  %in% unique(rd_output)]
drop_icuid<- setdiff(uni_id, uni_id_03)

AKI_lab_SC  <- AKI_lab %>%
  filter(FEATURE_NAME == "Creatinine", !(ICU_ID %in% drop_icuid))

AKI_lab_SC_adj <- AKI_lab_SC %>% 
  arrange(ICU_ID, RECORD_MIN) %>%  
  group_by(ICU_ID) %>%  
  filter(RECORD_MIN <= 60*24*7) %>%
  mutate(BASELINE_VALUE = first(na.omit(VALUE)),  
         BASELINE_TIME = first(RECORD_MIN), 
         VALUE_RATIO = VALUE / BASELINE_VALUE) %>%  
  mutate( 
    MAX_VALUE_2d = ifelse(RECORD_MIN <= 60*24*2, max(VALUE[RECORD_MIN <= 60*24*2], na.rm = TRUE), NA),
    Increase_VALUE_2d=ifelse(RECORD_MIN <= 60*24*2, (max(VALUE[RECORD_MIN <= 60*24*2], na.rm = TRUE)-BASELINE_VALUE), NA),
    MAX_VALUE_RATIO_7d = ifelse(RECORD_MIN <= 60*24*7, max(VALUE_RATIO, na.rm = TRUE), NA)) %>%  
  mutate(SC_CATEGORY = case_when( 
    BASELINE_TIME <= 60*24*2 & (MAX_VALUE_2d >= 4.0) ~ "S3-1",
    BASELINE_TIME <= 60*24*2 & (MAX_VALUE_RATIO_7d >= 3) ~ "S3-2",
    BASELINE_TIME <= 60*24*2 & MAX_VALUE_RATIO_7d >= 2 & MAX_VALUE_RATIO_7d < 3 ~ "S2", 
    BASELINE_TIME <= 60*24*2 & MAX_VALUE_RATIO_7d >= 1.5 & MAX_VALUE_RATIO_7d < 2 ~ "S1",
    TRUE ~ "unknown" 
  )) %>%
  summarise(SC_CATEGORY = first(SC_CATEGORY)) 

ICU_ID_SC_CATEGORY <- as.matrix(AKI_lab_SC_adj)
ICU_ID_SC_CATEGORY_14 <- as.data.frame(ICU_ID_SC_CATEGORY)
names(ICU_ID_SC_CATEGORY_14) <- c("ICU_ID", "SC_CATEGORY")
ICU_ID_SC_CATEGORY_14$ICU_ID <- as.integer(ICU_ID_SC_CATEGORY_14$ICU_ID)
#################################Main Test################################################


# import the dataset
lab_AKI_May_iv <- AKI_lab
# clean the dataset

codat = merge(ICU_ID_SC_CATEGORY_14, lab_AKI_May_iv, by = "ICU_ID")
codat = na.omit(codat)
# Basic functions
  
  km_cluster <- function(X) { 
    km <- Kmeans(X, 2, iter.max = 50, nstart=100,method = "manhattan")
    return(km$cluster)
  }
  
  hi_cluster <- function(X, meth =  "ward.D") {
    hc <- hclust(dist(X), meth)
    return(cutree(hc, k = 2))
  }
  
  sd_cluster <- function(X) {
    sd <- pam(X, 2)
    return(sd$clustering)
  }
  # function to compute the selective type I error
  test_clusters_approx_tensor <- function(X, k1, k2, iso=TRUE, sig=NULL, SigInv=NULL, ndraws=2000, cl_fun, cl=NULL) {
    if(!is.matrix(X)) stop("X should be a matrix")
    n <- nrow(X)
    q <- ncol(X)
    
    if(is.null(cl)) cl <- cl_fun(X)
    K <- length(unique(cl))
    
    if(!is_integer_between_a_b(K, 2, n)) stop("number of clusters (K) should be between 2 and n")
    if(!is_integer_between_a_b(k1, 1, K) | !is_integer_between_a_b(k2, 1, K)) stop(paste("cluster indices should be between 1 and K", sep=""))
    if((iso != TRUE) & (iso != FALSE)) stop("iso should be TRUE or FALSE")
    
    n1 <- sum(cl == k1)
    n2 <- sum(cl == k2)
    squared_norm_nu <- 1/n1 + 1/n2
    diff_means <- colMeans(X[cl == k1, , drop=FALSE]) - colMeans(X[cl == k2, , drop=F])
    
    prop_k2 <- n2/(n1+n2)
    
    
    if(iso) {
      if(is.null(sig)) {
        sig <- sqrt(sum(scale(X, scale=FALSE)^2)/(n*q - q))
      }
      
      scale_factor <- squared_norm_nu*sig^2
      # compute test statistic
      stat <- norm_vec(diff_means)
    } else {
      if(is.null(SigInv)) {
        Sig <- stats::cov(scale(X, scale=FALSE))
        SigInv <- solve(Sig)
      }
      
      scale_factor <- squared_norm_nu
      
      # compute test statistic
      stat <- sqrt(as.numeric(t(diff_means)%*%SigInv%*%diff_means))
    }
    
    scale_factor <- sqrt(scale_factor)
    phi <- stats::rnorm(ndraws)*scale_factor + stat
    
    
    k1_constant <- prop_k2*diff_means/stat
    k2_constant <- (prop_k2 - 1)*diff_means/stat
    orig_k1 <- t(X[cl == k1, ])
    orig_k2 <- t(X[cl == k2, ])
    
    Xphi <- X
    
    log_survives <- unlist(future.apply::future_lapply(X = 1:ndraws, FUN = function(j) {
      if(phi[j] < 0) return(NA)
      
      # Compute perturbed data set
      Xphi <- X
      Xphi[cl == k1, ] <- t(orig_k1 + (phi[j] - stat)*k1_constant)
      Xphi[cl == k2, ] <- t(orig_k2 + (phi[j] - stat)*k2_constant)
      
      # Recluster the perturbed data set
      cl_Xphi <- cl_fun(Xphi)
      if(preserve_cl(cl, cl_Xphi, k1, k2)) {
        log_survives <- -(phi[j]/scale_factor)^2/2 + (q-1)*log(phi[j]/scale_factor) - (q/2 - 1)*log(2) - lgamma(q/2) - log(scale_factor) -
          stats::dnorm(phi[j], mean=stat, sd=scale_factor, log=TRUE)
        return(log_survives)
      }
      
      return(NA)
      
    }, future.seed=TRUE))
    
    # Trim down to only survives
    phi <- phi[!is.na(log_survives)]
    log_survives <- log_survives[!is.na(log_survives)]
    
    survives <- length(log_survives)
    
    # Return nothing if nothing survives
    if(survives == 0) {
      warning("Oops - we didn't generate any samples that preserved the clusters! Try re-running with a larger value of ndraws.")
      return(list(stat=stat, pval=NA, stderr=NA, clusters=cl))
    }
    
    #  Approximate p-values
    log_survives_shift <- log_survives - max(log_survives)
    props <- exp(log_survives_shift)/sum(exp(log_survives_shift))
    pval <- sum(props[phi >= stat])
    
    var_pval <- (1 - pval)^2*sum(props[phi >= stat]^2) + pval^2*sum(props[phi < stat]^2)
    
    return(list(stat=stat, pval=pval, stderr=sqrt(var_pval), clusters=cl, n_survive = survives, phi = phi))
  }
  
  # ----- general purpose helper functions -----
  
  norm_vec <- function(x) {
    sqrt(sum(x^2))
  }
  
  is_integer_between_a_b <- function(x, a, b) {
    (x>= min(c(a, b))) && (x %% 1 == 0) && (x <= max(c(a, b)))
  }
  
  same_cl <- function(cl1, cl2, K) {
    tab <- table(cl1, cl2)
    sum(tab != 0) == K
  }
  
  preserve_cl <- function(cl, cl_phi, k1, k2) {
    tab <- table(cl, cl_phi)
    
    k1_in <- (sum(tab[k1, ] != 0) == 1) & (sum(tab[, k1] != 0) == 1)
    k2_in <- (sum(tab[k2, ] != 0) == 1) & (sum(tab[, k2] != 0) == 1)
    
    k1_in & k2_in
  }
  
  multivariate_Z_test <- function(X, k1, k2) { 
    q <- ncol(X)
    hcl <- sd_cluster(X)
    
    diff_means <- colMeans(X[hcl == k1, , drop=F]) - colMeans(X[hcl == k2, , drop=F])
    stat <- norm_vec(diff_means) 
    n1 <- sum(hcl == k1)  
    n2 <- sum(hcl == k2) 
    squared_norm_nu <- 1/n1 + 1/n2
    scale_factor <- squared_norm_nu
    
    pval <- 1 - pchisq(stat^2/scale_factor, df=q)
    return(list(stat=stat, pval=pval))
  }
  
  # compute selective pvalue
  
  
  #import library and set parameters

  rho<-0.999 
  draws_num<-20000
  lambd = 10^(-7)
  day = 7
  seed = 666
  rho1 = 0.5
  #m = nrow(dat_mat)/2 #number of patients
  m = 10000
  p = 3 #number of features
  X = seq(0,120,1)/120
  K = length(X)
  alpha = 0.5
  beta = 0.5
  deca = matrix(rep(1,K*K),K,K)
  for(i in seq(K)){
    for( j in seq(K)){
      u = max(i,j)
      v = min(i,j)
      if (u<=2*K/3 & v>K/3) deca[i,j] = (K-u)/(K+1)
      else deca[i,j] = 0.01
    }
  }
  
  kernel = function(X, rho = rho, K){
    sqdist = (matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))^2
    return(exp(-rho / (1-rho^2) * sqdist))
  }
  
  kernel_rq = function(X1, X2, rho = rho1,alpha = alpha){
    sqdist = (matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))^2
    return((1+rho/(1-rho^2)/alpha*sqdist)^(-alpha))
  }
  kernel_per = function(X1, X2, rho = rho1,beta = beta){
    sindist = sin(pi*abs(matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))/beta)^2
    return(exp(-2*sindist*rho/(1-rho^2)))
  }
  kernel_lpe = function(X1, X2, rho = rho1,beta = beta){
    dist = 2*sin(pi*abs(matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))/beta)^2+(matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))^2/2
    return(exp(-dist*rho/(1-rho^2)))
  }
  f = function(i,x){
    r = rep(0,length(x))
    N = 2^i*sqrt((1-rho)/(1+rho))*factorial(i)
    for(j in seq(length(x))){
      r[j] = exp(-rho/(1+rho)*x[j]^2)*hermite(x[j],i,prob = FALSE)/sqrt(N)
    }
    return(r)
  }
  
  mu = rep(0,K)
  cov = kernel(X, rho, K)
  cov_rq = kernel_rq(X,X,rho1,alpha)
  cov_per = kernel_per(X,X,rho1,beta)
  cov_lpe = kernel_lpe(X,X,rho1,beta)
  tsam = mvrnorm(m, mu, deca*cov)
  
  time = seq(0,1,1/(K-1))
  kernel_f = matrix(rep(0,p*K),p,K)
  for(i in seq(p)){
    kernel_f[i,] = f(i-1,time)
  }
  
  eigen = c()
  for(i in seq(p)){
    eigen = c(eigen, (1-rho)*rho**(i-1))
  }
  core_mat = diag(eigen)
  

  set.seed(seed)

  s1 = codat[codat$SC_CATEGORY == "S1",]
  s2 = codat[codat$SC_CATEGORY == "S2",]
  s3 = codat[codat$SC_CATEGORY == "S3-2",]
  s4 = codat[codat$SC_CATEGORY == "S3-1",]
  
  # set the day and truncate the dataset
  trun = 8
  multis1 = s1[s1$FEATURE_NAME == 'Creatinine',]
  d7multis1 = multis1[multis1$RECORD_MIN<=24*60*day,]
  d7multis1 = na.omit(d7multis1)
  
  multis2 = s2[s2$FEATURE_NAME == 'Creatinine',]
  d7multis2 = multis2[multis2$RECORD_MIN<=24*60*day,]
  d7multis2 = na.omit(d7multis2)
  
  multis3 = s3[s3$FEATURE_NAME == 'Creatinine',]
  d7multis3 = multis3[multis3$RECORD_MIN<=24*60*day,]
  d7multis3 = na.omit(d7multis3)
  
  multis4 = s4[s4$FEATURE_NAME == 'Creatinine',]
  d7multis4 = multis4[multis4$RECORD_MIN<=24*60*day,]
  d7multis4 = na.omit(d7multis4)
  
  feature = c('Creatinine')
  
  dattol = rbind(d7multis1)
  length(unique(d7multis1[d7multis1$FEATURE_NAME == feature[1],]$ICU_ID))
  
  pred = list()
  idsam = data.frame(c(unique(dattol[dattol$FEATURE_NAME == feature[1],]$ICU_ID)))
  names(idsam) = 'ICUID'
  
  rect1 = list()
  recv1 = list()
  
  for(fea in feature){
    print(fea)
    datcur = dattol[dattol$FEATURE_NAME == fea,]
    m = length(unique(datcur$ICU_ID))
    cursam = c()
    ida = 0
    
    for(id in 1:m){
      dcur = datcur[datcur$ICU_ID == unique(datcur$ICU_ID)[id],]
      K = length(dcur$RECORD_MIN)
      if(K <= trun) next
      ida = ida+1
      time = dcur$RECORD_MIN/(24*60*day)
      val = as.matrix(dcur$VALUE)
      #val = log(val/val[1])
      
      rect1[[ida]] = time
      recv1[[ida]] = val
      
      kercur = kernel(time,rho,K)
      kernel_f = matrix(rep(0,p*K),p,K)
      for(i in seq(p)){
        kernel_f[i,] = f(i-1,time)
      }
      mat1 = t(kernel_f)%*%core_mat
      inv1 = solve(kercur+lambd*diag(K))
      
      coef = t(val)%*%inv1
      if(anyNA(val)){
        print(val)
      }
      
      pred[[ida]] = coef%*%kercur
      cursam = c(cursam, unique(datcur$ICU_ID)[id],t(val)%*%t(solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f))#solve(t(kernel_f)%*%kernel_f+lambd*diag(K))%*%t(kernel_f))
    }
    cursam = t(array(cursam, dim = c(p+1, ida)))
    datf = data.frame(cursam)
    names(datf)[1] = 'ICUID'
    idsam = merge(idsam,datf, by = 'ICUID')
  }
  
  
  tol_sam1 = na.omit(as.matrix(idsam[,-1]))
  
  
  dattol = rbind(d7multis2)
  
  idsam = data.frame(c(unique(dattol[dattol$FEATURE_NAME == feature[1],]$ICU_ID)))
  names(idsam) = 'ICUID'
  
  rect2 = list()
  recv2 = list()
  
  for(fea in feature){
    print(fea)
    datcur = dattol[dattol$FEATURE_NAME == fea,]
    m = length(unique(datcur$ICU_ID))
    cursam = c()
    ida = 0
    
    for(id in 1:m){
      dcur = datcur[datcur$ICU_ID == unique(datcur$ICU_ID)[id],]
      K = length(dcur$RECORD_MIN)
      if(K <= trun) next
      ida = ida+1
      time = dcur$RECORD_MIN/(24*60*day)
      val = as.matrix(dcur$VALUE)
      #val = log(val/val[1])
      
      rect2[[ida]] = time
      recv2[[ida]] = val
      
      kercur = kernel(time,rho,K)
      kernel_f = matrix(rep(0,p*K),p,K)
      for(i in seq(p)){
        kernel_f[i,] = f(i-1,time)
      }
      mat1 = t(kernel_f)%*%core_mat
      inv1 = solve(kercur+lambd*diag(K))
      
      coef = t(val)%*%inv1
      if(anyNA(val)){
        print(val)
      }
      
      cursam = c(cursam, unique(datcur$ICU_ID)[id],t(val)%*%t(solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f))#solve(t(kernel_f)%*%kernel_f+lambd*diag(K))%*%t(kernel_f))
    }
    cursam = t(array(cursam, dim = c(p+1, ida)))
    datf = data.frame(cursam)
    names(datf)[1] = 'ICUID'
    idsam = merge(idsam,datf, by = 'ICUID')
  }
  
  tol_sam2 = na.omit(as.matrix(idsam[,-1]))
  
  
  
  
  
  dattol = rbind(d7multis3)
  
  idsam = data.frame(c(unique(dattol[dattol$FEATURE_NAME == feature[1],]$ICU_ID)))
  names(idsam) = 'ICUID'
  
  rect3 = list()
  recv3 = list()
  
  for(fea in feature){
    print(fea)
    datcur = dattol[dattol$FEATURE_NAME == fea,]
    m = length(unique(datcur$ICU_ID))
    cursam = c()
    ida = 0
    
    for(id in 1:m){
      dcur = datcur[datcur$ICU_ID == unique(datcur$ICU_ID)[id],]
      K = length(dcur$RECORD_MIN)
      if(K <= trun) next
      ida = ida+1
      time = dcur$RECORD_MIN/(24*60*day)
      val = as.matrix(dcur$VALUE)
      #val = log(val/val[1])
      
      rect3[[ida]] = time
      recv3[[ida]] = val
      
      kercur = kernel(time,rho,K)
      kernel_f = matrix(rep(0,p*K),p,K)
      for(i in seq(p)){
        kernel_f[i,] = f(i-1,time)
      }
      mat1 = t(kernel_f)%*%core_mat
      inv1 = solve(kercur+lambd*diag(K))
      
      coef = t(val)%*%inv1
      if(anyNA(val)){
        print(val)
      }
      
      cursam = c(cursam, unique(datcur$ICU_ID)[id],t(val)%*%t(solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f))#solve(t(kernel_f)%*%kernel_f+lambd*diag(K))%*%t(kernel_f))
    }
    cursam = t(array(cursam, dim = c(p+1, ida)))
    datf = data.frame(cursam)
    names(datf)[1] = 'ICUID'
    idsam = merge(idsam,datf, by = 'ICUID')
  }
  
  tol_sam3 = na.omit(as.matrix(idsam[,-1]))
  
  
  dattol = rbind(d7multis4)
  
  idsam = data.frame(c(unique(dattol[dattol$FEATURE_NAME == feature[1],]$ICU_ID)))
  names(idsam) = 'ICUID'
  
  rect4 = list()
  recv4 = list()
  
  for(fea in feature){
    print(fea)
    datcur = dattol[dattol$FEATURE_NAME == fea,]
    m = length(unique(datcur$ICU_ID))
    cursam = c()
    ida = 0
    
    for(id in 1:m){
      dcur = datcur[datcur$ICU_ID == unique(datcur$ICU_ID)[id],]
      K = length(dcur$RECORD_MIN)
      if(K <= trun) next
      ida = ida+1
      time = dcur$RECORD_MIN/(24*60*day)
      val = as.matrix(dcur$VALUE)
      #val = log(val/val[1])
      
      rect4[[ida]] = time
      recv4[[ida]] = val
      
      kercur = kernel(time,rho,K)
      kernel_f = matrix(rep(0,p*K),p,K)
      for(i in seq(p)){
        kernel_f[i,] = f(i-1,time)
      }
      mat1 = t(kernel_f)%*%core_mat
      inv1 = solve(kercur+lambd*diag(K))
      
      coef = t(val)%*%inv1
      if(anyNA(val)){
        print(val)
      }

      cursam = c(cursam, unique(datcur$ICU_ID)[id],t(val)%*%t(solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f))#solve(t(kernel_f)%*%kernel_f+lambd*diag(K))%*%t(kernel_f))
    }
    cursam = t(array(cursam, dim = c(p+1, ida)))
    datf = data.frame(cursam)
    names(datf)[1] = 'ICUID'
    idsam = merge(idsam,datf, by = 'ICUID')
  }
  
  tol_sam4 = na.omit(as.matrix(idsam[,-1]))
  
  
  ##########################Calculate the p-value#######################################
  sam_cov1 = solve(Re(sqrtm(cov(tol_sam1))))
  whit_samp1 = tol_sam1%*%sam_cov1
  cl = hi_cluster(whit_samp1)
  pva = test_clusters_approx_tensor(whit_samp1, k1=1, k2=2, cl_fun = hi_cluster, cl = cl, ndraws=draws_num)
  pva1<-pva$pval
  cp1<-multivariate_Z_test(whit_samp1, k1=1, k2=2)$pval
  ########################################################################
  sam_cov2 = solve(Re(sqrtm(cov(tol_sam2))))
  whit_samp2 = tol_sam2%*%sam_cov2
  cl = hi_cluster(whit_samp2)
  pva = test_clusters_approx_tensor(whit_samp2, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=draws_num)
  pva2<-pva$pval
  cp2<-multivariate_Z_test(whit_samp2, k1=1, k2=2)$pval
  ########################################################################
  sam_cov4 = solve(Re(sqrtm(cov(tol_sam4))))
  whit_samp4 = tol_sam4%*%sam_cov4
  cl = hi_cluster(whit_samp4)
  pva = test_clusters_approx_tensor(whit_samp4, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=draws_num)
  pva3<-pva$pval
  cp3<-multivariate_Z_test(whit_samp4, k1=1, k2=2)$pval
  ########################################################################
  sam_cov3 = solve(Re(sqrtm(cov(tol_sam3))))
  whit_samp3 = tol_sam3%*%sam_cov3
  cl =hi_cluster(whit_samp3)
  pva = test_clusters_approx_tensor(whit_samp3, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=draws_num)
  pva4<-pva$pval
  cp4<-multivariate_Z_test(whit_samp3, k1=1, k2=2)$pval
  ########################################################################
  tol_sam14 = rbind(tol_sam1, tol_sam4)
  sam_cov14 = solve(Re(sqrtm(cov(tol_sam14))))
  whit_samp14 = tol_sam14%*%sam_cov14
  cl = hi_cluster(whit_samp14)
  pva = test_clusters_approx_tensor(whit_samp14, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=draws_num)
  pva5<-pva$pval
  cp5<-multivariate_Z_test(whit_samp14, k1=1, k2=2)$pval
  ########################################################################
  tol_sam13 = rbind(tol_sam1, tol_sam3)
  sam_cov13 = solve(Re(sqrtm(cov(tol_sam13))))
  whit_samp13 = tol_sam13%*%sam_cov13
  cl = hi_cluster(whit_samp13)
  pva = test_clusters_approx_tensor(whit_samp13, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=draws_num)
  pva6<-pva$pval
  cp6<-multivariate_Z_test(whit_samp13, k1=1, k2=2)$pval
  ########################################################################
  tol_sam34 = rbind(tol_sam3, tol_sam4)
  sam_cov34 = solve(Re(sqrtm(cov(tol_sam34))))
  whit_samp34 = tol_sam34%*%sam_cov34
  cl = hi_cluster(whit_samp34)
  pva = test_clusters_approx_tensor(whit_samp34, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=draws_num)
  pva7<-pva$pval
  cp7<-multivariate_Z_test(whit_samp34, k1=1, k2=2)$pval
  ########################################################################
  ########################################################################
  
  TESTresults<-matrix(c(pva1,pva2,pva3,pva4,pva5,pva6,pva7,cp1,cp2,cp3,cp4,cp5,cp6,cp7),nrow=2 ,byrow=TRUE)
  colnames(TESTresults)<-c("S1","S2","S3-1","S3-2","(S1,S3-1)","(S1,S3-2)","(S3-1,S3-2)")
  row.names(TESTresults)<-c("PSIMF_p-value","Wald_p-value")

saveRDS(TESTresults,"../TESTresults2.rds")
print(TESTresults)







