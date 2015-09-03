Overheid::Application.routes.draw do
  root 'welcome#index'

  get 'nonce', to: 'api#nonce'
  post 'stem', to: 'api#stem'

  get 'index', to: 'welcome#index'
  get 'clear', to: 'welcome#clear'
end
