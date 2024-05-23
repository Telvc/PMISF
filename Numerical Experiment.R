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
library(sde)
library(rgl)

##########################Basic setup#######################################

# Basic functions

'
km_cluster(X): k-means clustering with manhattan distance,
hi_cluster(X): hierarchary clustering with full linkage,
sd_cluster(X): k-metriod clustering,
test_clusters_approx_tensor(X, k1, k2, ndraws, cl_fun, cl): compute the selective p-value for tensor data X (Section 3.4), where k1,k2 are labels of two clusters, ndraws is the number of samples for importance sampling, cl_fun is the clustering algorithm, cl is the label vector of all subjects.
'

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

# set parameters
'
lambda: user specified regularization term,
rho: smooth parameter of Gaussian RBF kernel
rho1, alpha: smooth parameters of RQ kernel
rho1, beta: smooth parameters of Per kernel & Lpe kernel
(See Section 5 for the detail explanation of RQ, Per and Lpe kernels)
'
  
  rho = 0.99
  lambd = 10^(-7)
  rho1 = 0.5
  alpha = 0.5
  beta = 0.5

# define kernel functions 
'
kernel(): gaussian RBF kernel 
kernel_rq(): RQ kernel
kernel per(): periodic kernel 
kernel_lpe(): local periodic kernel
f(i,x): the i-th Hermite polynomial with input x (i.e. we use Hermite polynomial as the basis in the embedding step)
'

  kernel = function(X, rho = rho, K){
    sqdist = (matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))^2
    return(exp(-rho / (1-rho^2) * sqdist))
  }
  
  kernel_rq = function(X, X2, rho = rho1,alpha = alpha){
    K = length(X)
    sqdist = (matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))^2
    return((1+rho/(1-rho^2)/alpha*sqdist)^(-alpha))
  }
  
  kernel_per = function(X, X2, rho = rho1,beta = beta){
    K = length(X)
    sindist = sin(pi*abs(matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))/beta)^2
    return(exp(-2*sindist*rho/(1-rho^2)))
  }
  
  kernel_lpe = function(X, X2, rho = rho1,beta = beta){
    K = length(X)
    dist = 2*sin(pi*abs(matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))/beta)^2+(matrix(rep(X,K),K,K)-t(matrix(rep(X,K),K,K)))^2/2
    mat0 = exp(-dist*rho/(1-rho^2))
    deca = matrix(rep(1,K*K),K,K)
    for(i in seq(K)){
      for( j in seq(K)){
        u = max(X[i],X[j])
        v = min(X[i],X[j])
        if (u<=2/3&v>1/3) deca[i,j] = 1
        else deca[i,j] = 0.01
      }
    }
    return(mat0*deca)
  }
  
  f = function(i,x){
    r = rep(0,length(x))
    N = 2^i*sqrt((1-rho)/(1+rho))*factorial(i)
    for(j in seq(length(x))){
      r[j] = exp(-rho/(1+rho)*x[j]^2)*hermite(x[j],i,prob = FALSE)/sqrt(N)
    }
    return(r)
  }

##########################Flow chart(Figure 2)#######################################
'
m: number of subjects
n_curve: number of feasibles
div: different in means between clusters
sig: variance of white noise
psize: number of basis used in the embedding step
'
  
  # plot the flow chart of H1
  
  m = 100000
  n_curve = 2
  div = 100
  psize = 2
  sig = 1
  
  sample_cl1 = div+mvrnorm(m/2, rep(0,n_curve*K), cov%x%diag(n_curve))+ sig*mvrnorm(m/2, rep(0,n_curve*K), diag(nrow(cov%x%diag(n_curve))))
  sample_cl2 = -div+mvrnorm(m/2, rep(0,n_curve*K), cov%x%diag(n_curve))+ sig*mvrnorm(m/2, rep(0,n_curve*K), diag(nrow(cov%x%diag(n_curve))))
  sample_cl = rbind(sample_cl1,sample_cl2)
  sample_cl = array(c(sample_cl), dim = c(m,n_curve, K))
  
  leng = c(1:25,(m/2+1):(m/2+25))
  mat = sample_cl[leng,1,]
  cl = km_cluster(sample_cl[,1,])
  long_df <- data.frame(
    index = rep(1:ncol(mat), each=nrow(mat)),
    value = as.vector(mat),
    variable = factor(rep(1:nrow(mat), times=ncol(mat))),
    lab = cl[leng]
  )
  
  ggplot(long_df, aes(x = index, y = value, group = variable, color = as.factor(lab),alpha = 1)) +
    geom_line(linewidth = 2) +
    theme_bw() + theme(legend.position = "none") + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize)) + xlim(1,T0+1)+
    theme(axis.title.x=element_blank(),
          axis.title.y=element_blank())
  
  coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
  tol_vec = array(0, dim = c(m, n_curve* p))
  
  for(i in seq(m)){
    tol_vec[i,] = array(sample_cl[i,,]%*%t(coe), dim = c(n_curve*p))
  }
  
  ggplot() + geom_point(aes(tol_vec[,1],tol_vec[,2], color = as.factor(cl)), size = psize)+
    theme_bw() + theme(legend.position = "none") + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))+
    theme(axis.title.x=element_blank(),
          axis.title.y=element_blank())
  
  whit = array(0, dim = c(m, n_curve,p))
  sam_cov = solve(Re(sqrtm(cov(tol_vec))))
  for(i in seq(m)){
    whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
  }
  whit_vec = matrix(whit, m, n_curve*p)
  
  ggplot() + geom_point(aes(whit_vec[,1],whit_vec[,2], color = as.factor(cl)), size = psize)+
    theme_bw() + theme(legend.position = "none") + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))+
    theme(axis.title.x=element_blank(),
          axis.title.y=element_blank())
  
  # plot of flow chart of H0
  
  sample_cl = mvrnorm(m, rep(0,n_curve*K), cov%x%diag(n_curve))+ sig*mvrnorm(m, rep(0,n_curve*K), diag(nrow(cov%x%diag(n_curve))))
  sample_cl = array(c(sample_cl), dim = c(m,n_curve, K))
  
  leng = c(1:25,251:275)
  mat = sample_cl[leng,1,]
  cl = km_cluster(sample_cl[,1,])
  long_df <- data.frame(
    index = rep(1:ncol(mat), each=nrow(mat)),
    value = as.vector(mat),
    variable = factor(rep(1:nrow(mat), times=ncol(mat))),
    lab = cl[leng]
  )
  
  ggplot(long_df, aes(x = index, y = value, group = variable, color = as.factor(lab),alpha = 1)) +
    geom_line(linewidth = 2) +
    theme_bw() + theme(legend.position = "none") + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize)) + xlim(1,T0+1)+
    theme(axis.title.x=element_blank(),
          axis.title.y=element_blank())
  
  coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
  tol_vec = array(0, dim = c(m, n_curve* p))
  
  for(i in seq(m)){
    tol_vec[i,] = array(t(sample_cl[i,,])%*%t(coe), dim = c(n_curve*p))
  }
  
  ggplot() + geom_point(aes(tol_vec[,1],tol_vec[,2], color = as.factor(cl)), size = psize)+
    theme_bw() + theme(legend.position = "none") + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))+
    theme(axis.title.x=element_blank(),
          axis.title.y=element_blank())
  
  whit = array(0, dim = c(m, n_curve,p))
  sam_cov = solve(sqrtm(cov(tol_vec)))
  for(i in seq(m)){
    whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
  }
  whit_vec = matrix(whit, m, n_curve*p)
  
  ggplot() + geom_point(aes(whit_vec[,1],whit_vec[,2], color = as.factor(cl)), size = psize)+
    theme_bw() + theme(legend.position = "none") + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))+
    theme(axis.title.x=element_blank(),
          axis.title.y=element_blank())
  
##########################Type-I error (Figure 5)#######################################
'
m: number of subjects
n_curve: number of feasibles
n_time: number of time points
div: different in means between clusters
M: number of iid data drawn to plot the QQ plot
sigm: a sequence of variance of white noise
psize: number of basis used in the embedding step
'  

  set.seed(120)
  m = 10000
  n_curve = 1
  n_time = 15
  div = 0
  M = 100
  sigm = c(0.01)
  err1 = c()
  
  # Time-Value plot(RQ kernel)
  
  n_time = 15
  t_record1 = sort(runif(n_time))
  t_record2 = sort(runif(n_time))
  t_record3 = sort(runif(n_time))
  t_record4 = sort(runif(n_time))
  t_record5 = sort(runif(n_time))
  cov_cur1 = kernel_rq(t_record1,t_record1,rho1,alpha)
  cov_cur2 = kernel_rq(t_record2,t_record2,rho1,alpha)
  cov_cur3 = kernel_rq(t_record3,t_record3,rho1,alpha)
  cov_cur4 = kernel_rq(t_record4,t_record4,rho1,alpha)
  cov_cur5 = kernel_rq(t_record5,t_record5,rho1,alpha)
  samp_cur1 = mvrnorm(1, rep(0,n_time), cov_cur1)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur1)))
  samp_cur2 = mvrnorm(1, rep(0,n_time), cov_cur2)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur2)))
  samp_cur3 = mvrnorm(1, rep(0,n_time), cov_cur3)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur3)))
  samp_cur4 = mvrnorm(1, rep(0,n_time), cov_cur4)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur4)))
  samp_cur5 = mvrnorm(1, rep(0,n_time), cov_cur5)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur5)))
  
  linesize = 1.5
  pointsize = 2.5
  axisize = 30
  titsize = 28
  
  ggplot() + geom_line(aes(t_record1,samp_cur1), color = 2,size = linesize)+ geom_line(aes(t_record2,samp_cur2), color = 3,size = linesize)+ geom_line(aes(t_record3,samp_cur3), color = 4,size = linesize)+ geom_line(aes(t_record4,samp_cur4), color = 5,size = linesize)+ geom_line(aes(t_record5,samp_cur5),size = linesize) + geom_point(aes(t_record1,samp_cur1), color = 2,size = pointsize)+ geom_point(aes(t_record2,samp_cur2), color = 3,size = pointsize)+ geom_point(aes(t_record3,samp_cur3), color = 4,size = pointsize)+ geom_point(aes(t_record4,samp_cur4), color = 5,size = pointsize)+ geom_point(aes(t_record5,samp_cur5),size = pointsize) + theme_bw() + xlab('Time') + ylab('Value') + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))
  
  # QQ plot (RQ kernel)
  for(sig in sigm){
    print(sig)
    type1err = 0
    pval = c()
    whit_samp = array(0, dim = c(M,m,n_curve,p))
    unwhit_samp = whit_samp
    for(j in seq(M)){
      coef = array(0, dim = c(m,n_curve, K))
      tol_sam = array(0, dim = c(m, n_curve, p))
      tol_vec = array(0, dim = c(m, n_curve* p))
      c_f_re = coef
      coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
      err = 0
      
      for(i in seq(m)){
        for(k in seq(n_curve)){
          t_record = sort(runif(n_time))
          cov_cur = kernel_rq(t_record,t_record,rho1,alpha)
          samp_cur = mvrnorm(1, rep(0,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
          kernel_cur = matrix(rep(0,p*n_time),p,n_time)
          for(l in seq(p)){
            kernel_cur[l,] = f(l-1,t_record)
          }
          coe_cur = solve(kernel_cur%*%t(kernel_cur)+lambd*diag(p))%*%kernel_cur
          tol_sam[i,k,] = samp_cur%*%t(coe_cur)
        }
        tol_vec[i,] = array(tol_sam[i,,], dim = c(n_curve*p))
      }
      
      if(j == 1) print(err)
      whit = array(0, dim = c(m, n_curve,p))
      sam_cov = solve(sqrtm(cov(tol_vec)))
      for(i in seq(m)){
        whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
      }
      whit_samp[j,,,] = whit
      unwhit_samp[j,,,] = tol_sam
      
      whit_vec = matrix(whit, m, n_curve*p)
      subset = sample(1:m,100,replace = FALSE)
      cl = hi_cluster(whit_vec[subset,])
      time = Sys.time()
      pva = test_clusters_approx_tensor(whit_vec[subset,], k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=1000)
      print(Sys.time()-time)
      pval = c(pval,pva$pval)
      print(j)
      print(pva$pval)
      if(pva$pval<= 0.05) type1err = type1err + 1
    }
    err1 = c(err1,type1err/M)
    print(err1)
  }
  
  sort_p = sort(pval)
  x = 1:M/M
  
  linesize = 0.5
  pointsize = 2
  axisize = 30
  titsize = 28
  
  ggplot() + geom_line(aes(x,x), color = "orange",size = pointsize) + geom_point(aes(x,quantile(sort_p,x)), color = "blue",size = pointsize) + theme_bw() + xlab("Theoretical quantile") + ylab("Empirical quantile") + ggtitle('Number of Time Points = 15') + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))
  
##########################Statistical Power (Figure 6)#######################################
  
  # statistical power with respect to sample size
  
  seed = 1
  power1 = c()
  power2 = c()
  
  # calculate the statistical power for sample size from 40 to 100
  
  for(i in c(4:10)){
    
    # set parameter
    
    m = 10*i
    n_curve = 1
    n_time = 10
    div = 10
    M = 100
    sigm = c(0.01)
    err1 = c()
    
    coef = array(0, dim = c(m,n_curve, K))
    tol_sam = array(0, dim = c(m, n_curve, p))
    tol_vec = array(0, dim = c(m, n_curve* p))
    c_f_re = coef
    coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
    
    # generate data and conduct the low-dimensional embedding step
    
    err = 0
    for(i in seq(m)){
      for(k in seq(n_curve)){
        t_record = sort(runif(n_time))
        cov_cur = kernel_per(t_record,t_record,rho1,alpha)
        if(i<=m/2){
          samp_cur = mvrnorm(1, rep(-div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
        } else {
          samp_cur = mvrnorm(1, rep(div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
        }
        kernel_cur = matrix(rep(0,p*n_time),p,n_time)
        for(l in seq(p)){
          kernel_cur[l,] = f(l-1,t_record)
        }
        coe_cur = solve(kernel_cur%*%t(kernel_cur)+lambd*diag(p))%*%kernel_cur
        tol_sam[i,k,] = samp_cur%*%t(coe_cur)
      }
      tol_vec[i,] = array(tol_sam[i,,], dim = c(n_curve*p))
    }
    
    # whittening step
    
    whit = array(0, dim = c(m, n_curve,p))
    sam_cov = solve(sqrtm(cov(tol_vec)))
    for(i in seq(m)){
      whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
    }
    
    whit_vec = matrix(whit, m, n_curve*p)
    cl0 = hi_cluster(whit_vec)
    
    # calculate the statistical power
    
    for(o in 1:15){
      set.seed(seed)
      seed = seed+1
      for(sig in sigm){
        print(sig)
        type1err = 0
        countp = 0
        pval = c()
        whit_samp = array(0, dim = c(M,m,n_curve,p))
        unwhit_samp = whit_samp
        for(j in seq(M)){
          
          coef = array(0, dim = c(m,n_curve, K))
          tol_sam = array(0, dim = c(m, n_curve, p))
          tol_vec = array(0, dim = c(m, n_curve* p))
          c_f_re = coef
          coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
          err = 0
          
          for(i in seq(m)){
            for(k in seq(n_curve)){
              t_record = sort(runif(n_time))
              cov_cur = kernel_per(t_record,t_record,rho1,alpha)
              if(i<=m/2){
                samp_cur = mvrnorm(1, rep(-div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
              } else {
                samp_cur = mvrnorm(1, rep(div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
              }
              kernel_cur = matrix(rep(0,p*n_time),p,n_time)
              for(l in seq(p)){
                kernel_cur[l,] = f(l-1,t_record)
              }
              coe_cur = solve(kernel_cur%*%t(kernel_cur)+lambd*diag(p))%*%kernel_cur
              tol_sam[i,k,] = samp_cur%*%t(coe_cur)
            }
            tol_vec[i,] = array(tol_sam[i,,], dim = c(n_curve*p))
          }
          
          if(j == 1) print(err)
          whit = array(0, dim = c(m, n_curve,p))
          sam_cov = solve(sqrtm(cov(tol_vec)))
          for(i in seq(m)){
            whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
          }
          whit_samp[j,,,] = whit
          unwhit_samp[j,,,] = tol_sam
          
          whit_vec = matrix(whit, m, n_curve*p)
          cl = hi_cluster(whit_vec)
          
          if(all(cl == cl0)){
            time = Sys.time()
            pva = test_clusters_approx_tensor(whit_vec, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=1000)
            pval = c(pval,pva$pval)
            countp = countp+1
            if(pva$pval<= 0.05) {
              type1err = type1err + 1
            }
          }
        }
        err1 = c(err1,type1err/M)
      }
      print(type1err/countp)
      if(countp != 0) power1 = c(power1, type1err/countp)
      else power1 = c(power1, NA)
    }
  }
  
  sample_sizes <- seq(40, 100, length.out = ncol(pow1))
  
    # Calculating means and confidence intervals
  means <- apply(pow1, 2, mean)
  
    # Standard error assuming normal distribution; adjust if another distribution is implied
  std_error <- apply(pow1, 2, sd) / sqrt(nrow(pow1))
  
    # Confidence interval (95% used here)
  alpha <- 0.05
  error_margin <- qt(1 - alpha/2, df=nrow(pow1)-1) * std_error
  lower_bounds <- means - error_margin
  upper_bounds <- means + error_margin
  
    # Preparing data for ggplot
  plot_data <- data.frame(
    SampleSize = sample_sizes,
    Mean = means,
    Lower = lower_bounds,
    Upper = upper_bounds
  )
  
    # Creating the plot
  ggplot(plot_data, aes(x = SampleSize, y = Mean)) +
    geom_line(color = "blue",linewidth = 2) +
    geom_point(color = "red") +
    geom_errorbar(aes(ymin = Lower, ymax = Upper), width = 2, color = "black") +
    labs(
      x = "Sample Size",
      y = "Statistical Power"
    ) +
    theme_bw()  + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))
  
  # statistical power with respect to cluster difference in means
  
    # set parameter
  
  power3 = c()
  power4 = c()
  
  sampletimes = 15
  m = 80
  n_curve = 1
  n_time = 15
  M = 1000
  sigm = c(0.01)
  sig = 0.01
  err1 = c()
  
    # calculate the statistical power for difference in means from 3.5 to 6.5
  
  for(s in c(3.5,4,4.5,5,5.5,6,6.5)){
    div = s
    
    coef = array(0, dim = c(m,n_curve, K))
    tol_sam = array(0, dim = c(m, n_curve, p))
    tol_vec = array(0, dim = c(m, n_curve* p))
    c_f_re = coef
    coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
    
    err = 0
    
      # generate data
    
    for(i in seq(m)){
      for(k in seq(n_curve)){
        t_record = sort(runif(n_time))
        cov_cur = kernel_per(t_record,t_record,rho1,alpha)
        if(i<=m/2){
          samp_cur = mvrnorm(1, rep(-div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
        } else {
          samp_cur = mvrnorm(1, rep(div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
        }
        kernel_cur = matrix(rep(0,p*n_time),p,n_time)
        for(l in seq(p)){
          kernel_cur[l,] = f(l-1,t_record)
        }
        coe_cur = solve(kernel_cur%*%t(kernel_cur)+lambd*diag(p))%*%kernel_cur
        tol_sam[i,k,] = samp_cur%*%t(coe_cur)
      }
      tol_vec[i,] = array(tol_sam[i,,], dim = c(n_curve*p))
    }
    
    whit = array(0, dim = c(m, n_curve,p))
    sam_cov = solve(sqrtm(cov(tol_vec)))
    for(i in seq(m)){
      whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
    }
    
    whit_vec = matrix(whit, m, n_curve*p)
    cl0 = hi_cluster(whit_vec)
    
      # calculate the statistical power
    
    for(o in 1:sampletimes){
      type1err = 0
      countp = 0
      pval = c()
      whit_samp = array(0, dim = c(M,m,n_curve,p))
      unwhit_samp = whit_samp
      for(j in seq(M)){
        
        coef = array(0, dim = c(m,n_curve, K))
        tol_sam = array(0, dim = c(m, n_curve, p))
        tol_vec = array(0, dim = c(m, n_curve* p))
        c_f_re = coef
        coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
        
        err = 0
        
        for(i in seq(m)){
          for(k in seq(n_curve)){
            t_record = sort(runif(n_time))
            cov_cur = kernel_per(t_record,t_record,rho1,alpha)
            if(i<=m/2){
              samp_cur = mvrnorm(1, rep(-div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
            } else {
              samp_cur = mvrnorm(1, rep(div,n_time), cov_cur)+ sig*mvrnorm(1, rep(0,n_time), diag(nrow(cov_cur)))
            }
            kernel_cur = matrix(rep(0,p*n_time),p,n_time)
            for(l in seq(p)){
              kernel_cur[l,] = f(l-1,t_record)
            }
            coe_cur = solve(kernel_cur%*%t(kernel_cur)+lambd*diag(p))%*%kernel_cur
            tol_sam[i,k,] = samp_cur%*%t(coe_cur)
          }
          tol_vec[i,] = array(tol_sam[i,,], dim = c(n_curve*p))
        }
        
        whit = array(0, dim = c(m, n_curve,p))
        sam_cov = solve(sqrtm(cov(tol_vec)))
        for(i in seq(m)){
          whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
        }
        
        whit_vec = matrix(whit, m, n_curve*p)
        cl = hi_cluster(whit_vec)
        cl
        
        if(all(cl == cl0)){
          time = Sys.time()
          pva = test_clusters_approx_tensor(whit_vec, k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=1000)
          pval = c(pval,pva$pval)
          countp = countp+1
          if(pva$pval<= 0.05) {
            type1err = type1err + 1
          }
        }
      }
      err1 = c(err1,type1err/M)
      
      print(countp)
      print(type1err/countp)
      if(countp != 0){
        power3 = c(power3, type1err/countp)
      } else {
        power3 = c(power3, NA)
      }
    }
  }
  
  pow2 = power3
  
  sample_sizes <- seq(3.5,6.5, length.out = ncol(pow2))
  
    # Calculating means and confidence intervals
  means <- apply(pow2, 2, mean)
  
    # Standard error assuming normal distribution; adjust if another distribution is implied
  std_error <- apply(pow2, 2, sd) / sqrt(nrow(pow2))
  
    # Confidence interval (95% used here)
  alpha <- 0.05
  error_margin <- qt(1 - alpha/2, df=nrow(pow2)-1) * std_error
  lower_bounds <- means - error_margin
  upper_bounds <- means + error_margin
  
    # Preparing data for ggplot
  plot_data <- data.frame(
    SampleSize = sample_sizes,
    Mean = means,
    Lower = lower_bounds,
    Upper = upper_bounds
  )
  
    # Creating the plot
  ggplot(plot_data, aes(x = SampleSize, y = Mean)) +
    geom_line(color = "blue",linewidth = 2) +
    geom_point(color = "red") +
    geom_errorbar(aes(ymin = Lower, ymax = Upper),width = 0.02, color = "black") +
    labs(
      x = "Difference in Cluster Mean",
      y = "Statistical Power"
    ) +
    theme_bw()  + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))
  
  
########################## Misspecification Case (Figure 7)#######################################
'
Calculate the type-I error for data generated by OU process/ exp brown process/ wierner process
mu11, sigma11: parameters related to exp brown process
mu12, theta12, sigma12: parameters related to OU process
'
  
  m = 10000
  n_curve = 1
  n_time = 15
  div = 0
  M = 100
  sigm = c(0.01)
  err1 = c()
  
  mu11 <- 0.1
  sigma11 <- 0.1
  theta12 <- 1.5
  mu12 <- 0.5
  sigma12 <- 0.3
  
  for(sig in sigm){
    
    type1err = 0
    pval = c()
    whit_samp = array(0, dim = c(M,m,n_curve,p))
    unwhit_samp = whit_samp
    
    for(j in seq(M)){
      
      coef = array(0, dim = c(m,n_curve, K))
      tol_sam = array(0, dim = c(m, n_curve, p))
      tol_vec = array(0, dim = c(m, n_curve* p))
      c_f_re = coef
      coe = solve(kernel_f%*%t(kernel_f)+lambd*diag(p))%*%kernel_f
      err = 0
      
      for(i in seq(m)){
        for(k in seq(n_curve)){
          t_record = sort(runif(n_time, min=0, max=1))
          
          #wierner process
          increments <- rnorm(n_time-1, mean = 0, sd = sqrt(diff(t_record)))
          samp_cur <- c(0, cumsum(increments))
          
          #OU process
          dt <- diff(c(0, t_record))
          samp_cur <- numeric(n_time)
          
          for (y in 2:n_time) {
            samp_cur[y] <- samp_cur[y-1] + theta12 * (mu12 - samp_cur[y-1]) * dt[y] + sigma12 * rnorm(1, sd=sqrt(dt[y]))
          }
          
          #exp brown motion
          samp_cur = exp(mu11 * t_record + sigma11 * rnorm(n_time, sd=sqrt(t_record)))
          
          kernel_cur = matrix(rep(0,p*n_time),p,n_time)
          for(l in seq(p)){
            kernel_cur[l,] = f(l-1,t_record)
          }
          coe_cur = solve(kernel_cur%*%t(kernel_cur)+lambd*diag(p))%*%kernel_cur
          tol_sam[i,k,] = samp_cur%*%t(coe_cur)
        }
        tol_vec[i,] = array(tol_sam[i,,], dim = c(n_curve*p))
      }
      
      if(j == 1) print(err)
      whit = array(0, dim = c(m, n_curve,p))
      sam_cov = solve(sqrtm(cov(tol_vec)))
      for(i in seq(m)){
        whit[i,,] = array(tol_vec[i,]%*%sam_cov, dim = c(n_curve,p))
      }
      whit_samp[j,,,] = whit
      unwhit_samp[j,,,] = tol_sam
      
      whit_vec = matrix(whit, m, n_curve*p)
      subset = sample(1:m,100,replace = FALSE)
      cl = hi_cluster(whit_vec[subset,])
      time = Sys.time()
      pva = test_clusters_approx_tensor(whit_vec[subset,], k1=1, k2=2, cl_fun=hi_cluster, cl = cl, ndraws=1000)
      print(Sys.time()-time)
      pval = c(pval,pva$pval)
      print(j)
      print(pva$pval)
      if(pva$pval<= 0.05) type1err = type1err + 1
    }
    err1 = c(err1,type1err/M)
    print(err1)
  }
  
  sort_p = sort(pval)
  x = 1:M/M
  
  ggplot() + geom_line(aes(x,x), color = "orange",size = pointsize) + geom_point(aes(x,quantile(sort_p,x)), color = "blue",size = pointsize) + theme_bw() + xlab("Theoretical quantile") + ylab("Empirical quantile") + theme(title=element_text(size=titsize),axis.text.x=element_text(size=axisize),axis.text.y=element_text(size=axisize))